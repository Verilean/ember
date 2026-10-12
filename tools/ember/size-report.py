#!/usr/bin/env python3
"""Size report and gate for the Ember stack (plan §3.5, §5).

    tools/ember/size-report.py            report, compare with the baseline
    tools/ember/size-report.py --update   re-record bench/ember-size.baseline

Builds the emitted C of the stack (Tests/Ember/golden/net.<profile>.c,
kept current by `lake test`):

* host64 — `gcc -Os -c`, sizes per function and per global from `nm -S`;
* sdcc-z80 — the image of runtime/z80 without tracing (`sdcc -mz80
  --opt-code-size`): ROM and RAM from the linker's area sizes, and the
  T-states per ICMP echo on the Z80 model (`ember-z80 ping`);
* esp32c3 — the bare-metal image of runtime/esp32c3 without tracing
  (`riscv32-none-elf-gcc -Os`): code, read-only data and RAM of the whole
  image (stack and runtime included, the 4 KB stack counted in the RAM),
  and the instructions per ICMP echo in Espressif's QEMU with `-icount`
  (when the cross compiler, esptool and that QEMU are installed).

Each metric must stay within ±3 % of the committed baseline, in either
direction (as bench/gate in Sparkle): a change in cost is a reviewed
diff of the baseline file.  Exit status 1 outside the tolerance.
"""
import importlib.util, os, re, subprocess, sys, tempfile, shutil

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
BASELINE = os.path.join(ROOT, "bench", "ember-size.baseline")
TOL = 0.03



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
    """The image of runtime/z80 as a board would run it: no trace, traps
    without their place (EMBER_TRACE=0, EMBER_TRAP_TERSE).  Code is
    everything in ROM (start-up, interrupt routine, runtime, the stack,
    SDCC's library routines, initialisers); RAM is the data without the
    stack."""
    if shutil.which("sdcc") is None or shutil.which("make") is None:
        return None
    src = os.path.join(ROOT, "Tests/Ember/golden/net.sdcc-z80.c")
    subprocess.run(["make", "-s", "-f", os.path.join(ROOT, "runtime/z80/Makefile"), "OUT=" + tmp,
                    "NAME=stack-quiet", "PROG=" + src, "DEFS=-DEMBER_TRACE=0 -DEMBER_TRAP_TERSE -DEMBER_NO_NAMES"], check=True)
    # area sizes are the linker's l__AREA symbols (the map repeats its
    # area header lines on every page: they must not be added up)
    sizes = {}
    with open(os.path.join(tmp, "stack-quiet.map")) as f:
        for line in f:
            m = re.match(r"^\s+([0-9A-F]{8})\s+l__(\w+)\s*$", line)
            if m:
                sizes["_" + m.group(2)] = int(m.group(1), 16)
    header = 0x100          # vectors and the jump to the start-up code
    code = header + sum(sizes.get(a, 0) for a in ("_HOME", "_CODE", "_INITIALIZER", "_GSINIT", "_GSFINAL"))
    ram = sizes.get("_DATA", 0) + sizes.get("_INITIALIZED", 0) + sizes.get("_BSS", 0)
    funcs = {}
    syms = []
    with open(os.path.join(tmp, "stack-quiet.noi")) as f:
        for line in f:
            m = re.match(r"^DEF (_\w+) 0x([0-9A-F]+)$", line)
            if m:
                syms.append((int(m.group(2), 16), m.group(1)))
    syms.sort()
    end = 0x100 + sizes.get("_CODE", 0)
    for (a, n), (b, _) in zip(syms, syms[1:] + [(end, "")]):
        if 0x100 <= a < end:
            funcs[n] = min(b, end) - a
    m = {"z80.code": code, "z80.ram": ram}
    exe = os.path.join(ROOT, ".lake/build/bin/ember-z80")
    if os.path.exists(exe):
        subprocess.run(["make", "-s", "-f", os.path.join(ROOT, "runtime/z80/Makefile"), "OUT=" + tmp,
                        "NAME=stack-tx", "PROG=" + src, "DEFS=-DEMBER_TRACE=1 -DEMBER_TRAP_TERSE -DEMBER_NO_NAMES"], check=True)
        out = subprocess.run([exe, "ping", os.path.join(tmp, "stack-tx.ihx")], check=True,
                             capture_output=True, text=True).stdout
        m["z80.ping_tstates"] = int(re.search(r"(\d+) T-states", out).group(1))
        # the stack is RAM too: its deepest point over the corpus
        out = subprocess.run([exe, "stack", os.path.join(tmp, "stack-quiet.ihx"), os.path.join(ROOT, "Tests/Ember/corpus")],
                             check=True, capture_output=True, text=True).stdout
        m["z80.stack"] = int(re.search(r"stack: (\d+) bytes", out).group(1))
    return m, funcs, sizes


def z80own(tmp):
    """The stack compiled by the own Z80 back end (plan M6), no trace: code
    with constants and runtime routines; static RAM (the runtime's cells and
    its 256-byte receive ring, globals, frames, temporaries — not the stack);
    the static bound on the stack and the deepest stack seen on the corpus
    (both with the interrupt routine's share); T-states per ping."""
    exe = os.path.join(ROOT, ".lake/build/bin/ember-z80")
    if not os.path.exists(exe):
        return None
    run = lambda *a: subprocess.run([exe, *a], check=True, capture_output=True, text=True, cwd=ROOT).stdout
    out = run("own-size", "net", "--trace", "0")
    g = re.search(r"(\d+) bytes of code and constants, (\d+) bytes of RAM", out)
    funcs = {mm.group(2): int(mm.group(1)) for mm in re.finditer(r"^\s+(\d+)\t(\S+)$", out, re.M)}
    m = {"z80own.code": int(g.group(1)), "z80own.ram": int(g.group(2))}
    # the static bound on the stack (start-up, the program, one interrupt); own-size fails
    # when it exceeds the room above the static RAM
    m["z80own.stack_bound"] = int(re.search(r"stack bound: (\d+) bytes", out).group(1))
    run("own-build", "net", "--trace", "0", "--out", os.path.join(tmp, "own0"))
    m["z80own.stack"] = int(re.search(r"stack: (\d+) bytes", run(
        "stack", os.path.join(tmp, "own0/net-own.ihx"), os.path.join(ROOT, "Tests/Ember/corpus"))).group(1))
    run("own-build", "net", "--trace", "1", "--out", os.path.join(tmp, "own1"))
    m["z80own.ping_tstates"] = int(re.search(r"(\d+) T-states", run("ping", os.path.join(tmp, "own1/net-own.ihx"))).group(1))
    return m, funcs


def esp32c3(tmp):
    """Sizes of the image a board runs (EMBER_TRACE=0) and instructions per ping."""
    need = ["riscv32-none-elf-gcc", "esptool", "make"]
    if any(shutil.which(t) is None for t in need):
        return None
    src = os.path.join(ROOT, "Tests/Ember/golden/net.rv32.c")
    mk = ["make", "-s", "-f", os.path.join(ROOT, "runtime/esp32c3/Makefile"), "OUT=" + tmp, "PROG=" + src]
    subprocess.run(mk + ["NAME=stack-quiet", "DEFS=-DEMBER_TRACE=0"], check=True)
    out = subprocess.run(["riscv32-none-elf-size", "-A", os.path.join(tmp, "stack-quiet.elf")],
                         check=True, capture_output=True, text=True).stdout
    sec = {m.group(1): int(m.group(2)) for m in re.finditer(r"^(\.\w+)\s+(\d+)", out, re.M)}
    nm = subprocess.run(["riscv32-none-elf-nm", "-S", "--size-sort", os.path.join(tmp, "stack-quiet.elf")],
                        check=True, capture_output=True, text=True).stdout
    funcs = {}
    for line in nm.splitlines():
        parts = line.split()
        if len(parts) == 4 and parts[2] in "Tt":
            funcs[parts[3]] = int(parts[1], 16)
    m = {"esp32c3.code": sec.get(".text", 0),
         "esp32c3.rodata": sec.get(".rodata", 0),
         "esp32c3.ram": sec.get(".data", 0) + sec.get(".bss", 0) + sec.get(".stack", 0)}
    if shutil.which("qemu-system-riscv32-esp") is not None:
        subprocess.run(mk + ["NAME=stack-icount", "DEFS=-DEMBER_TICK_HOST=1 -DEMBER_ICOUNT=1 -DEMBER_TRACE=1"], check=True)
        spec = importlib.util.spec_from_file_location("esp32", os.path.join(ROOT, "tools/ember/esp32.py"))
        esp32 = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(esp32)
        m["esp32c3.ping_instructions"] = esp32.measure_ping(images=tmp)[0]
    return m, funcs


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
            zm, zfuncs, areas = z
            metrics.update(zm)
            print("sdcc-z80 (--opt-code-size, no trace), areas:", ", ".join(f"{k}={v}" for k, v in sorted(areas.items()) if v))
            print("sdcc-z80, per symbol (bytes of code; library routines included):")
            for name, size in sorted(zfuncs.items(), key=lambda kv: -kv[1])[:25]:
                print(f"  {size:6d}  {name}")
            if "z80.ping_tstates" not in zm:
                print("sdcc-z80: .lake/build/bin/ember-z80 not built, T-states per ping skipped")
        else:
            print("sdcc-z80: sdcc/make not installed, skipped")
        o = z80own(tmp)
        if o is not None:
            om, ofuncs = o
            metrics.update(om)
            print("own Z80 back end (no trace), per function and runtime routine (bytes of code):")
            for name, size in sorted(ofuncs.items(), key=lambda kv: -kv[1])[:25]:
                print(f"  {size:6d}  {name}")
        else:
            print("own Z80 back end: .lake/build/bin/ember-z80 not built, skipped")
        e = esp32c3(tmp)
        if e is not None:
            em, funcs = e
            metrics.update(em)
            print("esp32c3 (riscv32-none-elf-gcc -Os, no trace), per function (bytes of code):")
            for name, size in sorted(funcs.items(), key=lambda kv: -kv[1])[:25]:
                print(f"  {size:6d}  {name}")
            if "esp32c3.ping_instructions" not in em:
                print("esp32c3: qemu-system-riscv32-esp not installed, instructions per ping skipped")
        else:
            print("esp32c3: riscv32-none-elf-gcc/esptool/make not installed, skipped")
        print("totals:")
        for k, v in metrics.items():
            print(f"  {k:26s} {v}")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    base = {}
    if os.path.exists(BASELINE):
        with open(BASELINE) as f:
            for line in f:
                if line.startswith("#") or not line.strip():
                    continue
                k, v = line.split()
                base[k] = int(v)
    if update:
        # a metric whose tool is missing here keeps its recorded value
        merged = dict(base)
        merged.update(metrics)
        with open(BASELINE, "w") as f:
            f.write("# Ember stack size baseline: tools/ember/size-report.py --update\n")
            for k, v in merged.items():
                f.write(f"{k} {v}\n")
        print(f"wrote {BASELINE}")
        return 0
    if not base:
        print("no baseline; run with --update")
        return 1
    for k in base:
        if k not in metrics:
            print(f"gate {k:26s} not measured here (tool missing)")
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
        print(f"gate {k:26s} {v:7d} vs {b:7d} ({delta:+.1%}) {status}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
