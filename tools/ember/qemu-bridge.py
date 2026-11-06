#!/usr/bin/env python3
"""An ESP32-C3 image in QEMU on stdin/stdout, as `ember-host` is (plan M8.4).

    tools/ember/qemu-bridge.py IMAGE.bin [--trace FILE]

Starts the image in Espressif's QEMU (`tools/ember/qemu-run.sh --dir`) and
relays bytes between stdin/stdout and UART0, where the image speaks SLIP;
what the image writes on UART1 (its trace) goes to FILE when given, and
is drained otherwise.  The image keeps its own time (SYSTIMER, 500 ms).
It is the `--host` of `tools/ember/record-linux.py client`, so that a Linux
client (curl, nc, ping) in a network namespace talks to the image:

    tools/ember/record-linux.py client --name curl-qemu --out /tmp \\
        --host "python3 tools/ember/qemu-bridge.py .lake/build/esp32c3/stack-http.bin" \\
        -- curl -sS http://10.0.0.1/

Runs inside nix-shell (QEMU).  Ends when stdin closes.
"""
import os, signal, socket, subprocess, sys, tempfile, threading, time

HERE = os.path.dirname(os.path.abspath(__file__))


def connect(path, timeout=20.0):
    end = time.time() + timeout
    while True:
        try:
            s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            s.connect(path)
            return s
        except OSError:
            s.close()
            if time.time() > end:
                sys.exit(f"qemu-bridge: no socket {path}")
            time.sleep(0.05)


def main():
    a = sys.argv[1:]
    if not a:
        sys.exit(__doc__)
    image, trace = a[0], None
    i = 1
    while i < len(a):
        if a[i] == "--trace" and i + 1 < len(a):
            trace = a[i + 1]; i += 2
        else:
            i += 1  # other options of ember-host are not ours
    d = tempfile.mkdtemp(prefix="ember-qemu-")
    # its own process group: qemu-run.sh does not exec QEMU, so stopping
    # the script alone would leave QEMU running
    qemu = subprocess.Popen(["sh", os.path.join(HERE, "qemu-run.sh"), image, "--dir", d],
                            stdout=subprocess.DEVNULL, stderr=sys.stderr, start_new_session=True)
    u0 = connect(os.path.join(d, "uart0.sock"))
    u1 = connect(os.path.join(d, "uart1.sock"))
    out = open(trace, "wb") if trace else None
    stop = threading.Event()

    def from_uart0():
        while not stop.is_set():
            b = u0.recv(4096)
            if not b:
                return
            os.write(1, b)

    def from_uart1():
        while not stop.is_set():
            b = u1.recv(4096)
            if not b:
                return
            if out:
                out.write(b)
                out.flush()

    threading.Thread(target=from_uart0, daemon=True).start()
    threading.Thread(target=from_uart1, daemon=True).start()
    while True:
        b = os.read(0, 4096)
        if not b:
            break
        u0.sendall(b)
    time.sleep(0.5)
    stop.set()
    os.killpg(qemu.pid, signal.SIGTERM)
    try:
        qemu.wait(5)
    except subprocess.TimeoutExpired:
        os.killpg(qemu.pid, signal.SIGKILL)
    if out:
        out.close()


if __name__ == "__main__":
    main()
