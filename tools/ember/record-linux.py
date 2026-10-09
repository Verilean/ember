#!/usr/bin/env python3
"""Record Ember trace fixtures from Linux, without root (plan §3.3).

Runs itself inside a user + network namespace (`unshare -rn`) and creates
a TUN device there.  Two modes:

  responder   Linux is 10.0.0.1, i.e. it plays Ember's role.  We inject
              the requests a peer at 10.0.0.2 would send (pings, UDP
              datagrams to an echo server on port 7) and record Linux's
              answers as the expected `tx` lines.  These fixtures say:
              "answer like Linux does".

  client      Linux is 10.0.0.2, the peer.  Packets on the TUN device are
              bridged (SLIP) to `ember-host`, the Spec stack at 10.0.0.1,
              while a command runs in the namespace (`ping`, `nc`).  The
              trace written by `ember-host --trace` is the fixture: inputs
              recorded from Linux, outputs from the Spec, and the command's
              success shows Linux accepted them.  `--eth` uses a TAP
              device and Ember's Ethernet + ARP link; `--dnsmasq RANGE`
              also runs dnsmasq on it and starts Ember with `--dhcp`.

  responder arp   Linux (with Ember's MAC) answers ARP on a TAP device.

Examples:
  tools/ember/record-linux.py responder icmp  Tests/Ember/corpus/icmp
  tools/ember/record-linux.py responder udp   Tests/Ember/corpus/udp
  tools/ember/record-linux.py client --name nc-echo --out Tests/Ember/corpus/tcp \\
      -- sh -c 'printf "hello\\n" | nc -N 10.0.0.1 7'
"""
import os, sys, struct, fcntl, select, socket, subprocess, threading, time, random

TUNSETIFF = 0x400454CA
IFF_TUN, IFF_TAP, IFF_NO_PI = 0x0001, 0x0002, 0x1000
EMBER_MAC = "02:00:00:00:00:01"
PEER_MAC = "02:00:00:00:00:02"
OURS, PEER = "10.0.0.1", "10.0.0.2"
END, ESC, ESC_END, ESC_ESC = 0xC0, 0xDB, 0xDC, 0xDD


def in_namespace():
    if os.environ.get("EMBER_NS") == "1":
        return
    env = dict(os.environ, EMBER_NS="1")
    os.execvpe("unshare", ["unshare", "-rn", sys.executable] + sys.argv, env)


def sh(*cmd):
    subprocess.run(cmd, check=True)


def open_tun(name, addr, peer, tap=False, mac=None):
    fd = os.open("/dev/net/tun", os.O_RDWR)
    kind = IFF_TAP if tap else IFF_TUN
    fcntl.ioctl(fd, TUNSETIFF, struct.pack("16sH", name.encode(), kind | IFF_NO_PI))
    for k in ("all", "default"):
        try:
            with open(f"/proc/sys/net/ipv6/conf/{k}/disable_ipv6", "w") as f:
                f.write("1")
        except OSError:
            pass
    sh("ip", "link", "set", "lo", "up")
    if tap:
        sh("ip", "link", "set", name, "address", mac)
        sh("ip", "addr", "add", addr + "/24", "dev", name)
    else:
        sh("ip", "addr", "add", addr, "peer", peer, "dev", name)
    sh("ip", "link", "set", name, "mtu", "576" if tap else "296", "up")
    return fd


def slip(pkt):
    out = bytearray([END])
    for b in pkt:
        out += bytes([ESC, ESC_END]) if b == END else bytes([ESC, ESC_ESC]) if b == ESC else bytes([b])
    out.append(END)
    return bytes(out)


def unslip(stream):
    frames, cur, esc = [], bytearray(), False
    for b in stream:
        if b == END:
            if cur:
                frames.append(bytes(cur))
            cur, esc = bytearray(), False
        elif esc:
            cur.append(END if b == ESC_END else ESC if b == ESC_ESC else b)
            esc = False
        elif b == ESC:
            esc = True
        else:
            cur.append(b)
    return frames, bytes(cur)


def csum(data):
    if len(data) % 2:
        data += b"\0"
    s = sum(struct.unpack("!%dH" % (len(data) // 2), data))
    while s >> 16:
        s = (s & 0xFFFF) + (s >> 16)
    return ~s & 0xFFFF


def ip_hdr(proto, src, dst, plen, ident):
    h = struct.pack("!BBHHHBBH4s4s", 0x45, 0, 20 + plen, ident, 0, 64, proto, 0,
                    socket.inet_aton(src), socket.inet_aton(dst))
    return h[:10] + struct.pack("!H", csum(h)) + h[12:]


def ping_pkt(ident, seq, payload, ipid):
    m = struct.pack("!BBHHH", 8, 0, 0, ident, seq) + payload
    m = m[:2] + struct.pack("!H", csum(m)) + m[4:]
    return ip_hdr(1, PEER, OURS, len(m), ipid) + m


def udp_pkt(sport, dport, data, ipid):
    ul = 8 + len(data)
    pseudo = socket.inet_aton(PEER) + socket.inet_aton(OURS) + struct.pack("!BBH", 0, 17, ul)
    u = struct.pack("!HHHH", sport, dport, ul, 0) + data
    c = csum(pseudo + u) or 0xFFFF
    u = u[:6] + struct.pack("!H", c) + u[8:]
    return ip_hdr(17, PEER, OURS, ul, ipid) + u


def hexs(b):
    return " ".join("%02x" % x for x in b)


class TraceWriter:
    def __init__(self, path, impl, note, mask=""):
        self.f = open(path, "w")
        m = f"  mask={mask}" if mask else ""
        self.f.write(f"# ember-trace v1  impl={impl}  build=linux-{os.uname().release}  profile=host64  link=slip{m}\n")
        for line in note:
            self.f.write(f"# {line}\n")
        self.step = 0

    def rx(self, b):
        self.f.write(f"{self.step:<6} rx   {hexs(b)}\n")

    def tx(self, b):
        self.f.write(f"{self.step:<6} tx   {hexs(b)}\n")

    def next(self):
        self.step += 1

    def close(self):
        self.f.close()


def read_replies(fd, wait=0.3):
    out, deadline = [], time.time() + wait
    while True:
        r, _, _ = select.select([fd], [], [], max(0, deadline - time.time()))
        if not r:
            return out
        p = os.read(fd, 65536)
        if p and p[0] >> 4 == 4:
            out.append(p)


def echo_servers():
    u = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    u.bind((OURS, 7))

    def run():
        while True:
            d, a = u.recvfrom(65536)
            u.sendto(d, a)
    threading.Thread(target=run, daemon=True).start()


def responder(kind, outdir):
    cmd = " ".join(sys.argv[1:])
    if kind == "arp":
        return responder_arp(outdir, cmd)
    fd = open_tun("tun0", OURS, PEER)
    echo_servers()
    os.makedirs(outdir, exist_ok=True)
    rnd = random.Random(1)
    cases = []
    if kind == "icmp":
        for size in (0, 56, 200):
            pk = []
            for seq in (1, 2, 3):
                stamp = (1760000000 + seq).to_bytes(8, "big") if size >= 8 else b""
                payload = (stamp + bytes(0x10 + i for i in range(max(0, size - 8))))[:size]
                pk.append(ping_pkt(0x4242, seq, payload, 0x1000 + seq))
            cases.append((f"linux-ping-s{size}", pk))
    elif kind == "udp":
        for n, size in enumerate((0, 1, 5, 64, 255)):
            data = bytes(rnd.randrange(256) for _ in range(size))
            cases.append((f"linux-udp-echo-{size}", [udp_pkt(40000 + n, 7, data, 0x2000 + n)]))
    else:
        sys.exit(f"unknown responder kind {kind}")
    for name, pkts in cases:
        tw = TraceWriter(os.path.join(outdir, name + ".trace"), "linux",
                         [f"recorded by: tools/ember/record-linux.py {cmd}",
                          f"Linux {os.uname().release} as 10.0.0.1 answering 10.0.0.2",
                          "IP identification is random in Linux: compared with mask=ipv4.id"],
                         mask="ipv4.id")
        for p in pkts:
            os.write(fd, p)
            tw.rx(slip(p))
            for r in read_replies(fd):
                tw.tx(slip(r))
            tw.next()
        tw.close()
        print("wrote", tw.f.name)


def mac_bytes(m):
    return bytes(int(x, 16) for x in m.split(":"))


def arp_req(sha, spa, tpa, op=1, tha=b"\0" * 6, dst=b"\xff" * 6):
    body = struct.pack("!HHBBH", 1, 0x0800, 6, 4, op) + sha + socket.inet_aton(spa) + tha + socket.inet_aton(tpa)
    return dst + sha + b"\x08\x06" + body


def eth_ip(dst, src, pkt):
    return dst + src + b"\x08\x00" + pkt


def read_frames(fd, wait=1.0):
    out, deadline = [], time.time() + wait
    while True:
        r, _, _ = select.select([fd], [], [], max(0, deadline - time.time()))
        if not r:
            return out
        p = os.read(fd, 65536)
        if len(p) >= 14 and p[12:14] in (b"\x08\x00", b"\x08\x06"):
            out.append(p)


def responder_arp(outdir, cmd):
    """Linux (10.0.0.1, MAC 02:..:01 — Ember's) on a TAP device."""
    fd = open_tun("tap0", OURS, None, tap=True, mac=EMBER_MAC)
    time.sleep(0.5)
    os.makedirs(outdir, exist_ok=True)
    peer, ours = mac_bytes(PEER_MAC), mac_bytes(EMBER_MAC)
    cases = [
        ("linux-arp-request", [arp_req(peer, PEER, OURS)]),
        ("linux-arp-other", [arp_req(peer, PEER, "10.0.0.9")]),
        ("linux-arp-then-ping", [arp_req(peer, PEER, OURS),
                                 eth_ip(ours, peer, ping_pkt(0x4343, 1, bytes(range(16, 72)), 0x3001)),
                                 eth_ip(ours, peer, ping_pkt(0x4343, 2, bytes(range(16, 72)), 0x3002))]),
    ]
    for name, frames in cases:
        path = os.path.join(outdir, name + ".trace")
        with open(path, "w") as f:
            f.write(f"# ember-trace v1  impl=linux  build=linux-{os.uname().release}  profile=host64  link=eth  mask=ipv4.id\n")
            f.write(f"# recorded by: tools/ember/record-linux.py {cmd}\n")
            f.write("# Linux as 10.0.0.1 with Ember's MAC on a TAP device; IP identification masked\n")
            for i, fr in enumerate(frames):
                os.write(fd, fr)
                f.write(f"{i:<6} rx   {hexs(fr)}\n")
                for r in read_frames(fd):
                    f.write(f"{i:<6} tx   {hexs(r)}\n")
        print("wrote", path)


def client(name, outdir, host_cmd, command, settle, eth=False, dnsmasq=None):
    if eth:
        fd = open_tun("tap0", PEER, None, tap=True, mac=PEER_MAC)
        host_cmd = host_cmd + ["--eth"]
    else:
        fd = open_tun("tun0", PEER, OURS)
    daemon = None
    if dnsmasq is not None:
        host_cmd = host_cmd + ["--dhcp"]
        daemon = subprocess.Popen(["dnsmasq", "--no-daemon", "--interface=tap0", "--bind-interfaces",
                                   "--no-resolv", "--no-hosts", "--port=0", "--no-ping",
                                   "--dhcp-leasefile=/dev/null", "--user=root",
                                   f"--dhcp-range={dnsmasq}"])
    os.makedirs(outdir, exist_ok=True)
    trace = os.path.join(outdir, name + ".trace")
    host = subprocess.Popen(host_cmd + ["--trace", trace], stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, bufsize=0)
    stop = threading.Event()

    def from_host():
        buf = b""
        while not stop.is_set():
            d = os.read(host.stdout.fileno(), 4096)
            if not d:
                return
            buf += d
            if eth:
                while len(buf) >= 2 and len(buf) >= 2 + int.from_bytes(buf[:2], "big"):
                    n = int.from_bytes(buf[:2], "big")
                    os.write(fd, buf[2:2 + n])
                    buf = buf[2 + n:]
            else:
                frames, buf = unslip(buf)
                for f in frames:
                    os.write(fd, f)
    threading.Thread(target=from_host, daemon=True).start()

    def to_host():
        while not stop.is_set():
            r, _, _ = select.select([fd], [], [], 0.1)
            if r:
                p = os.read(fd, 65536)
                if eth:
                    if len(p) >= 14 and p[12:14] in (b"\x08\x00", b"\x08\x06"):
                        host.stdin.write(len(p).to_bytes(2, "big") + p)
                        host.stdin.flush()
                elif p and p[0] >> 4 == 4:
                    host.stdin.write(slip(p))
                    host.stdin.flush()
    threading.Thread(target=to_host, daemon=True).start()
    time.sleep(0.3)
    rc = subprocess.run(command).returncode
    time.sleep(settle)
    stop.set()
    host.stdin.close()
    host.wait()
    if daemon:
        daemon.terminate()
    print(f"wrote {trace} (command exit {rc})")
    sys.exit(rc)


def main():
    in_namespace()
    a = sys.argv[1:]
    if not a:
        sys.exit(__doc__)
    if a[0] == "responder" and len(a) == 3:
        responder(a[1], a[2])
    elif a[0] == "client":
        name, out, host, settle, eth, dns = "session", ".", ["lake", "exe", "ember-host"], 1.0, False, None
        i = 1
        while i < len(a) and a[i] != "--":
            if a[i] == "--name": name = a[i + 1]; i += 2
            elif a[i] == "--out": out = a[i + 1]; i += 2
            elif a[i] == "--host": host = a[i + 1].split(); i += 2
            elif a[i] == "--settle": settle = float(a[i + 1]); i += 2
            elif a[i] == "--eth": eth = True; i += 1
            elif a[i] == "--dnsmasq": dns = a[i + 1]; eth = True; i += 2
            else: sys.exit(f"unknown option {a[i]}")
        client(name, out, host, a[i + 1:], settle, eth, dns)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
