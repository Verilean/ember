/* Ember runtime for the Z80, built with SDCC (plan M4z.2).
 *
 * A 68B50 ACIA at ports 0x80/0x81 carries SLIP; its receive interrupt
 * (interrupt mode 1) feeds the SPSC ring that the main loop drains.  The
 * ring and the interrupt routine are in crt0.s.  When the ring is nearly
 * full the routine raises RTS and the main loop lowers it again: a Z80
 * cannot take a SLIP frame at line rate while it computes checksums, the
 * sender has to wait.  A tick is an interrupt whose
 * source answers at port 0xC1 (bit 0 set while pending, reading clears
 * it); the trace goes to port 0xC0.  In the emulator (`Ember.Z80.Machine`)
 * those two ports are devices of their own; on a board they are whatever
 * timer and second serial port it has.
 *
 * EMBER_TRACE: 0 nothing on the debug port (traps only), 1 `tx N` after
 * every frame sent, 2 (default) also `drop` and `note` lines.
 */
#include "ember_rt.h"

#ifndef EMBER_TRACE
#define EMBER_TRACE 2
#endif

__sfr __at 0x80 ACIA_CTRL;                /* status when read */
__sfr __at 0x81 ACIA_DATA;
__sfr __at 0xC0 DBG;
__sfr __at 0xC1 TICK;

#define ACIA_TDRE 0x02
#define ACIA_RESET 0x03
#define ACIA_RUN  0x96                    /* receive interrupt, 8N1, clock/64, RTS low */
#define RING_LOW  128u                    /* lower RTS again at this fill */

/* the ring of crt0.s */
extern uint8_t rt_rx_buf[256];
extern volatile uint8_t rt_rx_head, rt_rx_tail, rt_rx_held, rt_ticks_pending;

void entry(void);
extern const char *const drop_names[];
extern const unsigned drop_names_count;
extern const char *const note_names[];
extern const unsigned note_names_count;

void main(void);

static uint8_t consumed;                  /* input items taken, modulo 256 */
static uint16_t frame_tx;

static void dbg_str(const char *s) { while (*s) DBG = (uint8_t)*s++; }

#if EMBER_TRACE >= 1
static void dbg_dec(uint16_t v) {
  static const uint16_t pow10[] = {10000u, 1000u, 100u, 10u};
  uint8_t started = 0;
  for (uint8_t i = 0; i < 4; i++) {
    uint8_t d = 0;
    while (v >= pow10[i]) { v -= pow10[i]; d++; }
    if (d || started) { DBG = (uint8_t)('0' + d); started = 1; }
  }
  DBG = (uint8_t)('0' + (uint8_t)v);
}
#endif

uint16_t ember_input_next(void) {
  if (rt_ticks_pending) {
    __asm__("di");
    rt_ticks_pending--;
    __asm__("ei");
    consumed++;
    return 0x0100u;
  }
  uint8_t t = rt_rx_tail;
  if (t == rt_rx_head) return 0xFFFFu;
  uint8_t b = rt_rx_buf[t];
  rt_rx_tail = (uint8_t)(t + 1u);
  if (rt_rx_held && (uint8_t)(rt_rx_head - rt_rx_tail) <= RING_LOW) {
    __asm__("di");
    rt_rx_held = 0;
    ACIA_CTRL = ACIA_RUN;
    __asm__("ei");
  }
  consumed++;
  return b;
}

uint16_t ember_ring_pop(void) { return ember_input_next(); }

void ember_out_byte(uint8_t b) {
  while (!(ACIA_CTRL & ACIA_TDRE)) {}
  ACIA_DATA = b;
  frame_tx++;
}

void ember_out_end(void) {
#if EMBER_TRACE >= 1
  dbg_str("tx "); dbg_dec(frame_tx); DBG = '\n';
#endif
  frame_tx = 0;
}

void ember_drop(uint8_t code) {
#if EMBER_TRACE >= 2
  dbg_str("drop reason=");
  if (code < drop_names_count) dbg_str(drop_names[code]);
  else { dbg_str("code-"); dbg_dec(code); }
  DBG = '\n';
#else
  (void)code;
#endif
}

void ember_note(uint8_t code, uint32_t value) {
#if EMBER_TRACE >= 2
  dbg_str("note ");
  if (code < note_names_count) dbg_str(note_names[code]);
  else { dbg_str("note-"); dbg_dec(code); }
  /* values above 65535 are printed modulo 65536 */
  DBG = ' '; dbg_dec((uint16_t)value); DBG = '\n';
#else
  (void)code; (void)value;
#endif
}

#ifdef EMBER_TRAP_TERSE
void ember_trap_terse(void) {
  dbg_str("note trap\n");
#else
void ember_trap(const char *where) {
  dbg_str("note trap "); dbg_str(where); DBG = '\n';
#endif
  for (;;) { __asm__("di"); __asm__("halt"); }
}

void main(void) {
  ACIA_CTRL = ACIA_RESET;
  ACIA_CTRL = ACIA_RUN;
  __asm__("ei");
  for (;;) {
    uint8_t before;
    do { before = consumed; entry(); } while (consumed != before);
    __asm__("di");
    if (rt_ticks_pending == 0 && rt_rx_head == rt_rx_tail) {
      /* nothing to do: sleep until an interrupt (EI acts after the HALT
       * has started, so no wake-up is lost) */
      __asm__("ei\nhalt");
    } else {
      __asm__("ei");
    }
  }
}
