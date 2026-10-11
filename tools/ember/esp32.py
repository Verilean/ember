#!/usr/bin/env python3
"""Host test driver for the Ember ESP32-C3 images in Espressif's QEMU (plan M4).

    tools/ember/esp32.py boot|trap|hello|echo|slip|corpus|tick|ping [options]

Each test starts QEMU on an image built by runtime/esp32c3/Makefile (see
tools/ember/qemu-test.sh, which builds them all and runs every test) with
UART0 and UART1 on unix sockets:

  boot    M4.0  the image boots and is still running at the timeout
  trap    M4.1  an illegal instruction prints `# trap cause=2 pc=...`
  hello   M4.2  "hello" on UART1
  echo    M4.3  10 000 random bytes, in bursts with random gaps, come back
                in order; the interrupt count is printed
  slip    M4.4  random SLIP frames through the Ember SLIP code
  corpus  M4.5, M4.6  every SLIP fixture replayed over the socket; the
                target's trace must equal the fixture (`ember-diff --drops`)
  tick    M4.6  the 500 ms SYSTIMER tick drives a SYN-ACK retransmission
  ping    M4.7  instructions per ICMP echo (QEMU -icount), for the gate

The target's trace is assembled here: the driver knows what it sent (the
`rx` and `tick` lines), UART0 gives the transmitted bytes, and UART1 says
how to cut them into frames (`tx N`), which diagnostics to add (`drop`,
`note`) and when the target has finished with its input (`# idle ...`).
"""
import argparse, os, random, re, select, shutil, socket, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
IMAGES = os.path.join(ROOT, ".lake", "build", "esp32c3")
QEMU = "qemu-system-riscv32-esp"
END, ESC, ESC_END, ESC_ESC = 0xC0, 0xDB, 0xDC, 0xDD


class TargetError(Exception):
    pass


class Target:
    """One QEMU instance running one image."""

    def __init__(self, image, icount=False, log=None, images=None):
        self.dir = tempfile.mkdtemp(prefix="ember-qemu-")
        flash = os.path.join(self.dir, "flash.bin")      # QEMU opens it for writing
        shutil.copyfile(os.path.join(images or IMAGES, image + ".bin"), flash)
        cmd = [QEMU, "-M", "esp32c3", "-display", "none", "-monitor", "none",
               "-drive", f"file={flash},if=mtd,format=raw"]
        for i in (0, 1):
            cmd += ["-serial", f"unix:{self.dir}/uart{i}.sock,server=on,wait=on"]
        if icount:
            cmd += ["-icount", "shift=0,sleep=off"]
        if log:
            cmd += ["-d", "int,guest_errors,unimp", "-D", log]
        self.proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
        self.u0 = self._connect(0)
        self.u1 = self._connect(1)
        self.out = bytearray()        # UART0 bytes not yet taken
        self.pending = b""            # partial UART1 line
        self.lines = []               # complete UART1 lines not yet taken
        self.log = []                 # every UART1 line, for error reports
        self.sent_rx = 0
        self.sent_tick = 0
        self.idle = {}

    def _connect(self, i):
        path = f"{self.dir}/uart{i}.sock"
        deadline = time.time() + 20
        while True:
            try:
                s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                s.connect(path)
                s.setblocking(False)
                return s
            except OSError:
                s.close()
                if self.proc.poll() is not None:
                    raise TargetError("QEMU exited: " + self.proc.stderr.read().decode(errors="replace"))
                if time.time() > deadline:
                    raise TargetError("QEMU did not open " + path)
                time.sleep(0.02)

    def close(self):
        if self.proc.poll() is None:
            self.proc.kill()
        self.proc.wait()
        self.proc.stderr.close()
        for s in (self.u0, self.u1):
            s.close()
        shutil.rmtree(self.dir, ignore_errors=True)

    def __enter__(self):
        return self

    def __exit__(self, *a):
        self.close()

    def pump(self, timeout):
        """Read whatever both UARTs have, waiting at most `timeout`."""
        r, _, _ = select.select([self.u0, self.u1], [], [], timeout)
        for s in r:
            try:
                data = s.recv(65536)
            except BlockingIOError:
                continue
            if not data:
                raise TargetError("QEMU closed a UART" + self.context())
            if s is self.u0:
                self.out += data
            else:
                parts = (self.pending + data).split(b"\n")
                self.pending = parts.pop()
                for p in parts:
                    line = p.decode(errors="replace").rstrip("\r")
                    self.lines.append(line)
                    self.log.append(line)
        return bool(r)

    def context(self):
        return "\n  last UART1 lines:\n    " + "\n    ".join(self.log[-8:])

    def line(self, timeout=10.0):
        """The next UART1 line."""
        deadline = time.time() + timeout
        while not self.lines:
            left = deadline - time.time()
            if left <= 0:
                raise TargetError(f"no UART1 line within {timeout} s" + self.context())
            self.pump(left)
        return self.lines.pop(0)

    def take(self, n, timeout=10.0):
        """The next `n` bytes of UART0."""
        deadline = time.time() + timeout
        while len(self.out) < n:
            left = deadline - time.time()
            if left <= 0:
                raise TargetError(f"UART0: {len(self.out)} of {n} bytes within {timeout} s" + self.context())
            self.pump(left)
        b = bytes(self.out[:n])
        del self.out[:n]
        return b

    def wait_ready(self, timeout=20.0):
        """The trace header: the image is up and listening.  Whatever came
        on UART0 before (the ROM's messages on a board) is dropped."""
        while True:
            l = self.line(timeout)
            if l.startswith("# ember-trace"):
                self.out.clear()
                return l
            if l.startswith("# trap"):
                raise TargetError(l)

    def send(self, data):
        self.u0.setblocking(True)
        self.u0.sendall(data)
        self.u0.setblocking(False)
        self.sent_rx += len(data)

    def request_tick(self):
        self.u1.setblocking(True)
        self.u1.sendall(b"t")
        self.u1.setblocking(False)
        self.sent_tick += 1

    def settle(self, timeout=30.0):
        """Events up to the idle line that accounts for everything sent."""
        events = []
        while True:
            l = self.line(timeout)
            if l == "tick":
                continue
            if l.startswith("tx "):
                events.append(("tx", self.take(int(l[3:]))))
            elif l.startswith("drop "):
                events.append(("drop", l[5:]))
            elif l.startswith("note trap") or l.startswith("# trap"):
                raise TargetError(l + self.context())
            elif l.startswith("note "):
                events.append(("note", l[5:]))
            elif l.startswith("# idle"):
                self.idle = {k: int(v) for k, v in re.findall(r"(\w+)=(\d+)", l)}
                if self.idle["rx"] >= self.sent_rx and self.idle["tick"] >= self.sent_tick:
                    return events
            else:
                raise TargetError("unexpected UART1 line: " + l + self.context())

    def rx(self, data):
        if not data:
            return []
        self.send(data)
        return self.settle()

    def tick(self):
        self.request_tick()
        return self.settle()


# ---- SLIP and traces --------------------------------------------------------

def slip_encode(payload):
    out = bytearray([END])
    for c in payload:
        if c == END:
            out += bytes([ESC, ESC_END])
        elif c == ESC:
            out += bytes([ESC, ESC_ESC])
        else:
            out.append(c)
    out.append(END)
    return bytes(out)


def read_fixture(path):
    """Header line and inputs ((None | bytes) per step: None is a tick)."""
    header, inputs = None, []
    with open(path) as f:
        for line in f:
            if line.startswith("#"):
                if header is None and "ember-trace" in line:
                    header = line.rstrip("\n")
                continue
            parts = line.split("#")[0].split()
            if len(parts) < 2:
                continue
            if parts[1] == "tick":
                inputs.append(None)
            elif parts[1] == "rx":
                inputs.append(bytes(int(x, 16) for x in parts[2:]))
    return header, inputs


def header_fields(header):
    return dict(kv.split("=", 1) for kv in header.split() if "=" in kv)


def supported(header):
    """As Ember.Tools.NetCheck.supported: the Ember stack is the SLIP build."""
    h = header_fields(header)
    return h.get("link", "slip") == "slip" and h.get("mtu", "296") == "296" and h.get("dhcp", "off") != "on"


def trace_line(step, kind, rest=""):
    return f"{step:<6} {kind:<4} {rest}".rstrip() if rest else f"{step:<6} {kind}"


def hexs(b):
    return " ".join(f"{x:02x}" for x in b)


def replay(image, header, inputs, icount=False):
    """Run the inputs on a fresh target; the trace text and the target."""
    lines = [re.sub(r"impl=\S+", "impl=esp32c3", re.sub(r"profile=\S+", "profile=rv32", header))]
    with Target(image, icount=icount) as t:
        t.wait_ready()
        for i, item in enumerate(inputs):
            if item is None:
                lines.append(trace_line(i, "tick"))
                events = t.tick()
            else:
                lines.append(trace_line(i, "rx", hexs(item)))
                events = t.rx(item)
            for kind, v in events:
                lines.append(trace_line(i, kind, hexs(v) if kind == "tx" else v))
        stats = dict(t.idle)
        if t.out:
            raise TargetError(f"{len(t.out)} bytes on UART0 outside any frame")
    return "\n".join(lines) + "\n", stats


# ---- tests --------------------------------------------------------------------

def test_boot(args):
    with Target("boot") as t:
        time.sleep(args.seconds)
        if t.proc.poll() is not None:
            raise TargetError("QEMU exited: " + t.proc.stderr.read().decode(errors="replace"))
    print(f"boot: still running after {args.seconds} s, stopped cleanly")


def test_trap(args):
    with Target("trap") as t:
        while True:
            l = t.line()
            if l.startswith("# trap"):
                break
    m = re.match(r"# trap cause=(\d+) pc=(0x[0-9a-f]{8}) tval=(0x[0-9a-f]{8})", l)
    if not m or m.group(1) != "2":
        raise TargetError("expected an illegal-instruction trap, got: " + l)
    print("trap:", l)


def test_hello(args):
    with Target("hello") as t:
        l = t.line()
    if l != "hello":
        raise TargetError("expected hello, got: " + l)
    print("hello: UART1 says hello")


def test_echo(args):
    rnd = random.Random(args.seed)
    data = bytes(rnd.randrange(256) for _ in range(args.bytes))
    got = bytearray()
    with Target("echo") as t:
        t.wait_ready()
        pos = 0
        while pos < len(data):
            # bursts up to several FIFOs and rings long, some sent in one
            # go and some byte by byte, with and without gaps
            n = rnd.choice([1, 1, 2, 7, 64, 128, 129, 300, 700, 1500])
            chunk = data[pos:pos + n]
            pos += len(chunk)
            t.send(chunk)
            if rnd.random() < 0.5:
                time.sleep(rnd.choice([0, 0.0005, 0.002, 0.01]))
                t.pump(0)
            else:
                t.settle()
                got += t.take(len(t.out))
        t.settle()
        got += t.take(len(t.out))
        idle = t.idle
    if bytes(got) != data:
        n = next((i for i in range(min(len(got), len(data))) if got[i] != data[i]), min(len(got), len(data)))
        raise TargetError(f"echo differs at byte {n}: got {len(got)} bytes of {len(data)}; idle {idle}")
    if idle["ovf"] != 0 or idle["rx"] != len(data) or idle["tx"] != len(data):
        raise TargetError(f"echo counters: {idle}")
    print(f"echo: {len(data)} bytes back in order; {idle['irq']} interrupts, {idle['ovf']} overruns")


def test_slip(args):
    rnd = random.Random(args.seed)
    frames = 0
    with Target("sliploop") as t:
        t.wait_ready()
        for k in range(args.frames):
            n = rnd.choice([1, 2, 20, 84, 295, 296]) if rnd.random() < 0.3 else rnd.randrange(1, 297)
            # plenty of END and ESC bytes in the payload
            payload = bytes(rnd.choice([END, ESC, ESC_END, ESC_ESC, rnd.randrange(256), rnd.randrange(256)])
                            for _ in range(n))
            wire = slip_encode(payload)
            if rnd.random() < 0.3:        # in pieces
                cut = rnd.randrange(1, len(wire))
                ev = t.rx(wire[:cut]) + t.rx(wire[cut:])
            else:
                ev = t.rx(wire)
            if ev != [("tx", wire)]:
                raise TargetError(f"frame {k} ({n} bytes): sent {wire.hex()} got {ev}")
            frames += 1
        # an oversize frame is dropped and the decoder recovers
        ev = t.rx(slip_encode(bytes(297)))
        if ev != [("drop", "reason=oversize-frame")]:
            raise TargetError(f"oversize frame: {ev}")
        ev = t.rx(slip_encode(b"after"))
        if ev != [("tx", slip_encode(b"after"))]:
            raise TargetError(f"frame after the oversize one: {ev}")
        idle = t.idle
    print(f"slip: {frames} random frames echoed, oversize frame dropped; {idle['irq']} interrupts")


def corpus_files(paths):
    out = []
    for p in paths:
        if os.path.isdir(p):
            for d, _, fs in sorted(os.walk(p)):
                out += [os.path.join(d, f) for f in sorted(fs) if f.endswith(".trace")]
        else:
            out.append(p)
    return out


def test_corpus(args):
    paths = args.paths or [os.path.join(ROOT, "Tests/Ember/corpus"), os.path.join(ROOT, "Tests/Ember/regress")]
    diff = os.path.join(ROOT, ".lake/build/bin/ember-diff")
    outdir = os.path.join(IMAGES, "traces")
    os.makedirs(outdir, exist_ok=True)
    todo, skipped = [], 0
    for f in corpus_files(paths):
        header, inputs = read_fixture(f)
        if header is None or not supported(header):
            skipped += 1
            continue
        if args.only and args.only not in f:
            continue
        todo.append((f, header, inputs))

    def one(job):
        f, header, inputs = job
        name = "-".join(f.split(os.sep)[-2:])
        out = os.path.join(outdir, name)
        try:
            text, _ = replay("stack-test", header, inputs)
        except TargetError as e:
            return f, False, str(e)
        with open(out, "w") as o:
            o.write(text)
        r = subprocess.run([diff, "--drops", f, out], capture_output=True, text=True)
        return f, r.returncode == 0, r.stdout + r.stderr

    bad = 0
    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for f, ok, report in ex.map(one, todo):
            rel = os.path.relpath(f, ROOT)
            if ok:
                if args.verbose:
                    print(f"ok   {rel}")
            else:
                bad += 1
                print(f"FAIL {rel}\n{report}")
    print(f"corpus: {len(todo) - bad} of {len(todo)} fixtures: target trace = Spec trace "
          f"({skipped} not for the SLIP build); traces in {os.path.relpath(outdir, ROOT)}")
    if bad:
        raise TargetError(f"{bad} fixtures differ")


def ip_packet(proto, payload, src=bytes([10, 0, 0, 2]), dst=bytes([10, 0, 0, 1]), ident=1):
    def csum(b):
        if len(b) % 2:
            b += b"\0"
        s = sum((b[i] << 8) | b[i + 1] for i in range(0, len(b), 2))
        while s >> 16:
            s = (s & 0xFFFF) + (s >> 16)
        return (~s) & 0xFFFF
    total = 20 + len(payload)
    h = bytearray([0x45, 0, total >> 8, total & 255, ident >> 8, ident & 255, 0, 0, 64, proto, 0, 0]) + src + dst
    c = csum(bytes(h))
    h[10], h[11] = c >> 8, c & 255
    return bytes(h) + payload, csum


def tcp_syn(sport=40000, seq=1000):
    seg = bytearray([sport >> 8, sport & 255, 0, 7]) + seq.to_bytes(4, "big") + bytes(4) + \
        bytearray([0x50, 0x02, 0x10, 0x00, 0, 0, 0, 0])
    _, csum = ip_packet(6, b"")
    pseudo = bytes([10, 0, 0, 2, 10, 0, 0, 1, 0, 6, 0, len(seg)])
    c = csum(pseudo + bytes(seg))
    seg[16], seg[17] = c >> 8, c & 255
    return ip_packet(6, bytes(seg))[0]


def test_tick(args):
    """The free-running 500 ms tick: an unanswered SYN-ACK is retransmitted
    after 3 ticks and then after 6 more (RTO back-off), in real time."""
    with Target("stack") as t:
        t.wait_ready()
        t0 = time.time()
        t.send(slip_encode(tcp_syn()))
        stamps = []
        while len(stamps) < 3:
            l = t.line(timeout=12)
            if l.startswith("tx "):
                t.take(int(l[3:]))
                stamps.append(time.time() - t0)
    first, second = stamps[1] - stamps[0], stamps[2] - stamps[1]
    print(f"tick: SYN-ACK at {stamps[0]:.2f} s, retransmitted after {first:.2f} s and {second:.2f} s more")
    # 3 ticks after a SYN that arrives anywhere within a tick period, then 6
    if not (0.9 <= first <= 1.7 and 2.8 <= second <= 3.3):
        raise TargetError("retransmission times are not 3 and 6 ticks of 500 ms")


def ping_request(n=56, seq=1):
    icmp = bytearray([8, 0, 0, 0, 0x12, 0x34, seq >> 8, seq & 255]) + bytes(i & 255 for i in range(n))
    _, csum = ip_packet(1, b"")
    c = csum(bytes(icmp))
    icmp[2], icmp[3] = c >> 8, c & 255
    return ip_packet(1, bytes(icmp), ident=seq)[0]


def measure_ping(count=8, images=None):
    """Instructions per 56-byte ICMP echo, from the request's first byte
    to idle again (receive interrupts, the stack, the polled transmit and
    the `tx` trace line), by QEMU's instruction counter: the median of
    `count` pings on one target."""
    costs = []
    with Target("stack-icount", icount=True, images=images) as t:
        t.wait_ready()
        t.rx(slip_encode(ping_request(seq=1)))            # warm-up: `booted`
        for k in range(count):
            before = t.idle["ins"]
            ev = t.rx(slip_encode(ping_request(seq=2 + k)))
            if len(ev) != 1 or ev[0][0] != "tx":
                raise TargetError(f"ping not answered: {ev}")
            costs.append(t.idle["ins"] - before)
    costs.sort()
    return costs[len(costs) // 2], costs


def test_ping(args):
    median, costs = measure_ping()
    print(f"ping: {median} instructions per 56-byte echo (median of {len(costs)}: {costs})")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="test", required=True)
    p = sub.add_parser("boot"); p.add_argument("--seconds", type=float, default=2.0)
    sub.add_parser("trap")
    sub.add_parser("hello")
    p = sub.add_parser("echo"); p.add_argument("--bytes", type=int, default=10000); p.add_argument("--seed", type=int, default=1)
    p = sub.add_parser("slip"); p.add_argument("--frames", type=int, default=300); p.add_argument("--seed", type=int, default=1)
    p = sub.add_parser("corpus")
    p.add_argument("paths", nargs="*")
    p.add_argument("--jobs", type=int, default=min(8, os.cpu_count() or 1))
    p.add_argument("--only", default="")
    p.add_argument("--verbose", action="store_true")
    sub.add_parser("tick")
    sub.add_parser("ping")
    args = ap.parse_args()
    if shutil.which(QEMU) is None:
        print(f"{QEMU} not found (run inside nix-shell)")
        return 2
    try:
        globals()["test_" + args.test](args)
    except TargetError as e:
        print(f"FAIL {args.test}: {e}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
