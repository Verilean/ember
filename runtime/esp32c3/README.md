# Ember on the ESP32-C3, bare metal (M4)

The emitted stack (`Tests/Ember/golden/net.rv32.c`) with a runtime of
three files: no ESP-IDF, no RTOS, no C library.

| File | Contents |
|---|---|
| `start.S` | reset entry (stack, `mtvec`, `.bss`), the vector table, trap entry |
| `link.ld` | code in IRAM from `0x40380000`, data in DRAM from `0x3FC90000` (64 KB each), 4 KB stack |
| `soc.h` | the registers used: UART0/1, interrupt matrix, SYSTIMER, watchdogs, clock gates, GPIO matrix |
| `rt.c` | watchdogs off, UART0 receive interrupt → SPSC ring, polled transmit, SYSTIMER tick, the trace on UART1, trap handler, main loop |
| `Makefile` | `NAME.elf`, `NAME.map`, `NAME.img` (ESP image, loaded into RAM by the ROM boot loader) and `NAME.bin` (the same, padded to a 4 MB flash image for QEMU) |

UART0 carries SLIP and nothing else.  UART1 is the debug channel
(plan §3.5); what it prints is described at the top of `rt.c`.

## Running in QEMU

Everything below is inside `nix-shell` (Espressif's QEMU fork comes from
`tools/ember/nix/qemu-esp32c3.nix`, their release binary; nixpkgs' QEMU
has no ESP32 machine).

```
tools/ember/qemu-test.sh                 # build all images, run all tests (≈ 40 s)
tools/ember/qemu-test.sh corpus --verbose
tools/ember/qemu-run.sh .lake/build/esp32c3/hello.bin --timeout 3
tools/ember/qemu-run.sh .lake/build/esp32c3/stack.bin --dir /tmp/e --gdb --log
```

| Test (`tools/ember/esp32.py …`) | Step | What it shows |
|---|---|---|
| `boot` | M4.0 | the image boots and runs until stopped |
| `trap` | M4.1 | an illegal instruction prints `# trap cause=2 pc=… tval=…` |
| `hello` | M4.2 | polled output on UART1 |
| `echo` | M4.3 | 10 000 random bytes in bursts of 1 to 1 500 with random gaps come back in order, no overruns; interrupt count printed |
| `slip` | M4.4 | 300 random SLIP frames (full of END/ESC bytes, some split) through the Ember SLIP code (`Ember.Net.Loop`); an oversize frame is dropped |
| `corpus` | M4.5, M4.6 | every SLIP fixture of the corpus: target trace = fixture (`ember-diff --drops`: `rx`, `tx`, `tick` and drop reasons) |
| `corpus DIR` | | the same for sessions written by `ember-lockstep --gen … --dump DIR` |
| `tick` | M4.6 | with the free-running 500 ms tick, an unanswered SYN-ACK is retransmitted after 1.5 s and 3 s |
| `ping` | M4.7 | instructions per 56-byte echo (`-icount`) |

### How a fixture is replayed

The driver sends a step's `rx` bytes on UART0, or for a `tick` the byte
`t` on UART1; the target answers on UART1 with `tx N` for every frame
it sent, its `drop`/`note` lines, and `# idle rx=R tick=T …` once it has
consumed everything.  The driver cuts UART0's bytes into frames with the
`tx N` lines and writes a §3.1 trace, which `ember-diff` compares with
the fixture.

The images differ only in build flags:

| Image | Flags | Use |
|---|---|---|
| `stack` | — | 500 ms tick from SYSTIMER, full trace |
| `stack-test` | `EMBER_TICK_HOST=1` | a tick when the host asks (still through the SYSTIMER interrupt), so that fixtures with ticks replay deterministically |
| `stack-icount` | + `EMBER_ICOUNT=1` | instruction counter in the idle line |
| `stack-quiet` | `EMBER_TRACE=0` | nothing on UART1 but traps: what a board runs, and what the size gate measures |

## Size and cost (`tools/ember/size-report.py`, `bench/ember-size.baseline`)

| | |
|---|---|
| code (`.text`, runtime included) | 7.0 KB |
| read-only data | 0.8 KB |
| RAM (`.data` + `.bss` + 4 KB stack) | 5.0 KB |
| instructions per 56-byte ping | 16 634 |

Budget (plan M4): code < 16 KB, RAM < 8 KB.

## Receive path

The UART raises its interrupt as soon as one byte is in its FIFO (and
after two idle symbol times); the ISR moves the FIFO into the 256-byte
ring.  When the ring is full the ISR masks the interrupt and leaves the
bytes in the UART's 128-byte FIFO; the main loop unmasks it once it has
taken a byte.  Transmission is polled from the main loop, so a long
reply does not block reception, only the consumption of the ring.

## On a board (M4.8) — not done

No ESP32-C3 was available; the steps below are untested.  QEMU does not
model the clock tree, the pads or the baud rate, so `uart1_init` (clock
gate, 115200 from the 40 MHz crystal, GPIO4 = TX, GPIO5 = RX) and the
assumption that the ROM leaves UART0 at 115200 on GPIO20/21 are checked
only against the reference manual.

```
esptool --chip esp32c3 --port /dev/ttyUSB0 write-flash 0x0 .lake/build/esp32c3/stack-quiet.img
sudo slattach -s 115200 -p slip /dev/ttyUSB0 &
sudo ip addr add 10.0.0.2 peer 10.0.0.1 dev sl0 && sudo ip link set sl0 up mtu 296
ping -c 3 10.0.0.1 && printf 'hello\n' | nc -N 10.0.0.1 7
```

The ROM prints its boot messages on UART0 before the image starts; the
SLIP peer sees them as one malformed frame.
