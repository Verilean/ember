/* Ember runtime interface: what emitted code calls (design §2.4).
 *
 * The runtime is hand-written and part of the trusted base.  On a target
 * it is start-up code, the UART ISR feeding an SPSC ring, and the timer;
 * on the host (Tests/Ember/host/harness.c) it is an input oracle reading
 * a trace file and a trace writer.  The protocol logic is all in the
 * emitted code. */
#ifndef EMBER_RT_H
#define EMBER_RT_H

#include <stdint.h>
#include <stdbool.h>

/* Next input item: 0x00..0xFF a byte, 0x0100 a tick, 0xFFFF nothing. */
uint16_t ember_input_next(void);
uint16_t ember_ring_pop(void);
/* On a link that delivers whole frames: as ember_input_next, and 0x0200
 * after the last byte of each frame. */
uint16_t ember_input_frame(void);

/* Transmit: bytes of the current frame, then end of frame. */
void ember_out_byte(uint8_t b);
void ember_out_end(void);

/* Diagnostics (drop reasons and notes are tables in the emitted code). */
void ember_drop(uint8_t code);
void ember_note(uint8_t code, uint32_t value);

uint32_t ember_mmio_read32(uint32_t addr);
void ember_mmio_write32(uint32_t addr, uint32_t value);

#if defined(__GNUC__)
#define EMBER_NORETURN __attribute__((noreturn))
#elif defined(__SDCC)
#define EMBER_NORETURN _Noreturn
#else
#define EMBER_NORETURN
#endif

/* A bounds check failed; `where` names the Ember function and statement.
 * Does not return (and saying so lets the optimiser, and -Warray-bounds,
 * know that the access after a failed check is unreachable).
 *
 * With EMBER_TRAP_TERSE the names are not compiled in (they are a
 * kilobyte of strings, a lot on a Z80): the trap is reported without
 * its place. */
#ifdef EMBER_TRAP_TERSE
EMBER_NORETURN void ember_trap_terse(void);
#define ember_trap(where) ember_trap_terse()
#else
EMBER_NORETURN void ember_trap(const char *where);
#endif

#endif
