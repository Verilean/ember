/* `mmio.read32`/`mmio.write32` for programs that use them on the Z80,
 * which has no memory-mapped devices: a small table that remembers what
 * was written, as the host harness and the interpreter do. */
#include "ember_rt.h"

static uint32_t addr[8], val[8];
static uint8_t n;

uint32_t ember_mmio_read32(uint32_t a) {
  for (uint8_t i = 0; i < n; i++) if (addr[i] == a) return val[i];
  return 0;
}

void ember_mmio_write32(uint32_t a, uint32_t v) {
  for (uint8_t i = 0; i < n; i++) if (addr[i] == a) { val[i] = v; return; }
  if (n < 8) { addr[n] = a; val[n] = v; n++; }
}
