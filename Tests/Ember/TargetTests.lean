/-!
# M4 tests: the emitted stack on the ESP32-C3 in Espressif's QEMU

`tools/ember/qemu-test.sh` builds the bare-metal images
(`runtime/esp32c3`) and runs, over QEMU's UART sockets: boot, trap
handler, UART output, interrupt-driven byte echo (10 000 bytes), SLIP
loopback through the Ember SLIP code, the SLIP corpus and generated
sessions (target trace = Spec trace), and the SYSTIMER tick.  Skipped
when the cross compiler, esptool, make or that QEMU is not installed
(they come with `nix-shell`).
-/

namespace Ember.Tests.TargetTests

def installed (cmd : String) (arg := "--version") : IO Bool := do
  try
    let r ← IO.Process.output { cmd, args := #[arg] }
    return r.exitCode == 0
  catch _ => return false

def main : IO UInt32 := do
  for t in ["riscv32-none-elf-gcc", "qemu-system-riscv32-esp", "make", "python3"] do
    if !(← installed t) then
      IO.println s!"esp32c3: {t} not installed, skipped"
      return 0
  if !(← installed "esptool" "version") then
    IO.println "esp32c3: esptool not installed, skipped"
    return 0
  let r ← IO.Process.output { cmd := "tools/ember/qemu-test.sh" }
  IO.print r.stdout
  if r.exitCode != 0 then
    IO.eprint r.stderr
    IO.println "FAIL esp32c3: tools/ember/qemu-test.sh"
    return 1
  return 0

end Ember.Tests.TargetTests
