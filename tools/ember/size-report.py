#!/usr/bin/env python3
"""Size report and gate for the Ember stack (plan §3.5, §5).

    tools/ember/size-report.py            report, compare with the baseline
    tools/ember/size-report.py --update   re-record bench/ember-size.baseline

Builds the emitted C of the stack (Tests/Ember/golden/net.<profile>.c,
kept current by `lake test`):

* host64 — `gcc -Os -c`, sizes per function and per global from `nm -S`;
* sdcc-z80 — `sdcc -mz80 --opt-code-size`, linked with a stub runtime,
  CODE and DATA totals from the map file (when SDCC is installed).

Each metric must stay within ±3 % of the committed baseline, in either
direction (as bench/gate in Sparkle): a change in cost is a reviewed
diff of the baseline file.  Exit status 1 outside the tolerance.
"""
import os, re, subprocess, sys, tempfile, shutil

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BASELINE = os.path.join(ROOT, "bench", "ember-size.baseline")
TOL = 0.03

STUB = r'''
#include "ember_rt.h"
uint16_t ember_input_next(void) { return 0xFFFFu; }
uint16_t ember_ring_pop(void) { return 0xFFFFu; }
void ember_out_byte(uint8_t b) { (void)b; }
void ember_out_end(void) {}
void ember_drop(uint8_t c) { (void)c; }
void ember_note(uint8_t c, uint32_t v) { (void)c; (void)v; }
uint32_t ember_mmio_read32(uint32_t a) { (void)a; return 0; }
void ember_mmio_write32(uint32_t a, uint32_t v) { (void)a; (void)v; }
void ember_trap(const char *w) { (void)w; for (;;) {} }
void entry(void);
int main(void) { for (;;) entry(); }
'''


def host64(tmp):
    src = os.path.join(ROOT, "Tests/Ember/golden/net.host64.c")
    obj = os.path.join(tmp, "net.o")
    subprocess.run(["gcc", "-std=c99", "-Os", "-ffunction-sections", "-fdata-sections",
                    "-I" + os.path.join(ROOT, "runtime/common"), "-c", src, "-o", obj], check=True)
    out = subprocess.run(["nm", "-S", "--size-sort", obj], check=True, capture_output=True, text=True).stdout
    code, ram, rodata = {}, {}, {}
    for line in out.splitlines():
        parts = line.split()
        if len(parts) != 4:
            continue
        size, kind, name = int(parts[1], 16), parts[2], parts[3]
        k = kind.upper()
        if k == "T":
            code[name] = size
        elif k in "BD":
            ram[name] = size
        elif k == "R":
            rodata[name] = size
    return code, ram, rodata


def z80(tmp):
    if shutil.which("sdcc") is None:
        return None
    src = os.path.join(ROOT, "Tests/Ember/golden/net.sdcc-z80.c")
    stub = os.path.join(tmp, "stub.c")
    with open(stub, "w") as f:
        f.write(STUB)
    inc = "-I" + os.path.join(ROOT, "runtime/common")
    flags = ["-mz80", "--std-c99", "--opt-code-size", "--disable-warning", "110", "--disable-warning", "126", inc]
    subprocess.run(["sdcc"] + flags + ["-c", src, "-o", os.path.join(tmp, "net.rel")], check=True)
    subprocess.run(["sdcc"] + flags + ["-c", stub, "-o", os.path.join(tmp, "stub.rel")], check=True)
    subprocess.run(["sdcc", "-mz80", "--code-loc", "0x0100", "--data-loc", "0x8000",
                    os.path.join(tmp, "stub.rel"), os.path.join(tmp, "net.rel"),
                    "-o", os.path.join(tmp, "net.ihx")], check=True)
    sizes = {}
    with open(os.path.join(tmp, "net.map")) as f:
        for line in f:
            m = re.match(r"^(_\w+)\s+([0-9A-F]{8})\s+([0-9A-F]{8})\s*=\s*(\d+)\.\s*bytes", line)
            if m:
                sizes[m.group(1)] = sizes.get(m.group(1), 0) + int(m.group(4))
    # the stack's own areas only: the stub is tiny, and the C library is
    # pulled in by 32/64-bit arithmetic (counted, it is part of the cost)
    code = sizes.get("_CODE", 0) + sizes.get("_HOME", 0) + sizes.get("_INITIALIZER", 0)
    ram = sizes.get("_DATA", 0) + sizes.get("_INITIALIZED", 0)
    return code, ram, sizes


def main():
    update = "--update" in sys.argv
    tmp = tempfile.mkdtemp(prefix="ember-size-")
    try:
        code, ram, rodata = host64(tmp)
        metrics = {
            "host64.code": sum(code.values()),
            "host64.ram": sum(ram.values()),
            "host64.rodata": sum(rodata.values()),
        }
        print("host64 (gcc -Os), per function (bytes of code):")
        for name, size in sorted(code.items(), key=lambda kv: -kv[1]):
            print(f"  {size:6d}  {name}")
        print("host64, RAM per global (bytes):")
        for name, size in sorted(ram.items(), key=lambda kv: -kv[1]):
            print(f"  {size:6d}  {name}")
        z = z80(tmp)
        if z is not None:
            zc, zr, areas = z
            metrics["z80.code"] = zc
            metrics["z80.ram"] = zr
            print("sdcc-z80 (--opt-code-size), areas:", ", ".join(f"{k}={v}" for k, v in sorted(areas.items())))
        else:
            print("sdcc-z80: sdcc not installed, skipped")
        print("totals:")
        for k, v in metrics.items():
            print(f"  {k:16s} {v}")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    if update:
        with open(BASELINE, "w") as f:
            f.write("# Ember stack size baseline: tools/ember/size-report.py --update\n")
            for k, v in metrics.items():
                f.write(f"{k} {v}\n")
        print(f"wrote {BASELINE}")
        return 0
    if not os.path.exists(BASELINE):
        print("no baseline; run with --update")
        return 1
    base = {}
    with open(BASELINE) as f:
        for line in f:
            if line.startswith("#") or not line.strip():
                continue
            k, v = line.split()
            base[k] = int(v)
    bad = 0
    for k, v in metrics.items():
        if k not in base:
            print(f"  {k}: no baseline value")
            continue
        b = base[k]
        delta = (v - b) / b if b else 0.0
        status = "ok" if abs(delta) <= TOL else "OUTSIDE ±3%"
        if status != "ok":
            bad += 1
        print(f"gate {k:16s} {v:7d} vs {b:7d} ({delta:+.1%}) {status}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
