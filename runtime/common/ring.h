/* Single-producer / single-consumer byte ring (design §2.2).
 *
 * The receive ISR is the only writer of `head`, the main loop the only
 * writer of `tail`; each index is read by the other side.  With a
 * power-of-two size and 8-bit indices no lock is needed on targets whose
 * byte stores are atomic (Z80, RISC-V).  The ring's specification is
 * `Ember.Spec`-style: the main loop sees the received bytes in order,
 * minus those dropped when the ring was full (counted in `overruns`). */
#ifndef EMBER_RING_H
#define EMBER_RING_H

#include <stdint.h>

#define EMBER_RING_SIZE 256u   /* must be a power of two, at most 256 */

typedef struct {
  volatile uint8_t head;      /* written by the producer (ISR) */
  volatile uint8_t tail;      /* written by the consumer */
  volatile uint16_t overruns;
  uint8_t buf[EMBER_RING_SIZE];
} ember_ring;

static inline void ember_ring_push_isr(ember_ring *r, uint8_t b) {
  uint8_t h = r->head;
  uint8_t next = (uint8_t)((h + 1u) & (EMBER_RING_SIZE - 1u));
  if (next == r->tail) { r->overruns++; return; }
  r->buf[h] = b;
  r->head = next;
}

/* 0x00..0xFF a byte, 0xFFFF empty. */
static inline uint16_t ember_ring_take(ember_ring *r) {
  uint8_t t = r->tail;
  if (t == r->head) return 0xFFFFu;
  uint8_t b = r->buf[t];
  r->tail = (uint8_t)((t + 1u) & (EMBER_RING_SIZE - 1u));
  return b;
}

#endif
