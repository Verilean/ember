/* Test harness for emitted Ember code on the Z80 (plan M4z.1): the
 * counterpart of Tests/Ember/host/harness.c.
 *
 * Not a runtime for a board: the input oracle and the event recorder are
 * ports of the emulator (`Ember.Z80.Machine`), so that any Ember program
 * — the examples, random programs — runs exactly as in the interpreter:
 * the entry is called while input remains, and the run ends after three
 * calls in a row that consume nothing.  The image holds several
 * programs (the table `ember_progs`); port 0xD8 says which one to run.
 */
#include "ember_rt.h"

__sfr __at 0xD0 H_REMAINS;
__sfr __at 0xD1 H_TAKE;
__sfr __at 0xD2 H_BYTE;
__sfr __at 0xD3 H_OUT;
__sfr __at 0xD4 H_END;
__sfr __at 0xD5 H_DROP;
__sfr __at 0xD6 H_NOTE;
__sfr __at 0xD7 H_TRAP;
__sfr __at 0xD8 H_PROGRAM;

typedef struct { void (*entry)(void); const char *const *drops; const unsigned *ndrops;
                 const char *const *notes; const unsigned *nnotes; const unsigned *framed; } ember_prog;
extern const ember_prog ember_progs[];

void main(void);

static uint8_t consumed;

uint16_t ember_input_next(void) {
  uint8_t kind = H_TAKE;
  if (kind == 2) return 0xFFFFu;
  consumed++;
  if (kind == 1) return 0x0100u;
  return H_BYTE;
}

uint16_t ember_ring_pop(void) { return ember_input_next(); }
void ember_out_byte(uint8_t b) { H_OUT = b; }
void ember_out_end(void) { H_END = 0; }
void ember_drop(uint8_t code) { H_DROP = code; }
void ember_note(uint8_t code, uint32_t value) { (void)value; H_NOTE = code; }

void ember_trap(const char *where) {
  (void)where;
  H_TRAP = 0;
  for (;;) { __asm__("di"); __asm__("halt"); }
}

void main(void) {
  void (*entry)(void) = ember_progs[H_PROGRAM].entry;
  uint8_t idle = 0;
  while (H_REMAINS && idle < 3) {
    uint8_t before = consumed;
    entry();
    idle = (consumed == before) ? (uint8_t)(idle + 1) : 0;
  }
}
