#!/usr/bin/env python3
"""Client-side scenarios run by record-linux.py in client mode (Linux is
10.0.0.2, the Spec stack 10.0.0.1).  Each exits 0 when Linux saw the
behaviour the scenario expects."""
import socket, struct, sys, time

E = ("10.0.0.1", 7)


def recv_exact(s, n, timeout=5):
    s.settimeout(timeout)
    out = b""
    while len(out) < n:
        d = s.recv(n - len(out))
        if not d:
            break
        out += d
    return out


def echo(data):
    s = socket.create_connection(E, timeout=5)
    s.sendall(data)
    got = recv_exact(s, len(data))
    s.shutdown(socket.SHUT_WR)
    rest = recv_exact(s, 1)
    s.close()
    return got == data and rest == b""


def bulk():
    data = bytes((i * 7) % 251 for i in range(2000))
    s = socket.create_connection(E, timeout=5)
    s.sendall(data)
    got = recv_exact(s, len(data))
    s.close()
    time.sleep(0.5)
    return got == data


def client_rst():
    s = socket.create_connection(E, timeout=5)
    s.sendall(b"bye")
    recv_exact(s, 3)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
    s.close()
    return True


def server_close():
    s = socket.create_connection(E, timeout=60)
    s.sendall(b"ping\n")
    ok = recv_exact(s, 5) == b"ping\n"
    s.settimeout(60)
    eof = s.recv(1) == b""          # the echo server closes when idle
    s.close()
    return ok and eof


def second_connection():
    a = socket.create_connection(E, timeout=5)
    try:
        socket.create_connection(E, timeout=5)
        refused = False
    except ConnectionRefusedError:
        refused = True
    a.sendall(b"one")
    ok = recv_exact(a, 3) == b"one"
    a.close()
    time.sleep(0.5)
    return refused and ok


def closed_port():
    try:
        socket.create_connection(("10.0.0.1", 8), timeout=5)
        return False
    except ConnectionRefusedError:
        return True


def two_sessions():
    ok = echo(b"first\n")
    time.sleep(0.5)
    return ok and echo(b"second\n")


def udp_echo():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.settimeout(3)
    ok = True
    for n in (1, 100, 268):
        d = bytes(range(256)) * 2
        s.sendto(d[:n], ("10.0.0.1", 7))
        ok = ok and s.recvfrom(2048)[0] == d[:n]
    return ok


SCENARIOS = {
    "echo": lambda: echo(b"hello, ember\n"),
    "bulk": bulk,
    "client-rst": client_rst,
    "server-close": server_close,
    "second-connection": second_connection,
    "closed-port": closed_port,
    "two-sessions": two_sessions,
    "udp-echo": udp_echo,
}

if __name__ == "__main__":
    ok = SCENARIOS[sys.argv[1]]()
    print(sys.argv[1], "ok" if ok else "FAILED")
    sys.exit(0 if ok else 1)
