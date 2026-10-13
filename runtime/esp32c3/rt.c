/* Ember runtime for the ESP32-C3, bare metal (plan M4).
 *
 * No ESP-IDF, no RTOS: start.S, this file and the emitted stack are the
 * whole image.  UART0 carries SLIP; its receive interrupt feeds the SPSC
 * ring that the main loop drains (design §2.2).  UART1 carries the trace
 * (plan §3.5), and SYSTIMER comparator 0 gives the 500 ms `tick`.
 *
 * Build-time choices:
 *   APP          APP_STACK (default): run the emitted program's entry()
 *                APP_ECHO:  echo UART0 bytes (M4.3, no Ember code)
 *                APP_HELLO: print "hello" on UART1 (M4.2)
 *                APP_TRAP:  execute an illegal instruction (M4.1)
 *                APP_BOOT:  nothing but the start-up (M4.0)
 *   EMBER_TRACE  0: UART1 silent (traps only)
 *                1: + `tick`, `tx N` and `# idle ...` lines, which let a
 *                   host driver cut UART0's bytes into trace steps
 *                2: + `drop` and `note` lines (default)
 *   EMBER_TICK_HOST  0: a tick every EMBER_TICK_MS (default 500)
 *                1: one tick per byte 't' received on UART1 — still
 *                   delivered by the SYSTIMER interrupt, but when the
 *                   host says, so that fixtures replay deterministically
 *   EMBER_ICOUNT 1: `ins=` in the idle line is the number of instructions
 *                retired so far, interrupts included, writing the idle
 *                lines excluded (QEMU with -icount; `minstret` is not a
 *                C3 CSR)
 *
 * UART1 lines (EMBER_TRACE >= 1):
 *   # ember-trace v1  impl=esp32c3 ...     once, when ready for input
 *   tick                                   a tick was consumed
 *   tx N                                   a frame of N bytes went out on UART0
 *   drop reason=NAME / note NAME VALUE     diagnostics
 *   # idle rx=R tick=T tx=X irq=I ovf=O ins=N
 *                                          all input so far is processed:
 *                                          R bytes and T ticks consumed,
 *                                          X bytes sent
 *   # trap cause=C pc=0x.. tval=0x.. rx=R tick=T
 *                                          CPU exception after R bytes and
 *                                          T ticks; the image halts
 */
#include "soc.h"
#include "ember_rt.h"
#include "ring.h"

#define APP_STACK 0
#define APP_ECHO  1
#define APP_HELLO 2
#define APP_TRAP  3
#define APP_BOOT  4
#ifndef APP
#define APP APP_STACK
#endif
#ifndef EMBER_TRACE
#define EMBER_TRACE 2
#endif
#ifndef EMBER_TICK_HOST
#define EMBER_TICK_HOST 0
#endif
#ifndef EMBER_TICK_MS
#define EMBER_TICK_MS 500u
#endif
#ifndef EMBER_ICOUNT
#define EMBER_ICOUNT 0
#endif
/* UART1 pins on a board (QEMU ignores them) */
#ifndef EMBER_U1TX_GPIO
#define EMBER_U1TX_GPIO 4u
#endif
#ifndef EMBER_U1RX_GPIO
#define EMBER_U1RX_GPIO 5u
#endif

#define LINE_UART0 1u
#define LINE_UART1 2u
#define LINE_SYSTIMER 3u

void rt_main(void);
void rt_trap(uint32_t cause, uint32_t epc, uint32_t tval);
void *memcpy(void *d, const void *s, unsigned n);
void *memset(void *d, int c, unsigned n);

/* the emitted program */
void entry(void);
extern const char *const drop_names[];
extern const unsigned drop_names_count;
extern const char *const note_names[];
extern const unsigned note_names_count;

static ember_ring rx;
static volatile uint8_t rx_paused;        /* ring full: bytes wait in the UART's FIFO */
static volatile uint32_t irq_count;
static volatile uint32_t ticks_pending;
static volatile uint32_t tick_req;        /* EMBER_TICK_HOST: ticks asked for, not yet fired */
static uint32_t n_rx, n_tick, n_tx, frame_tx;

/* gcc may call these for struct copies */
void *memcpy(void *d, const void *s, unsigned n) {
  uint8_t *a = d; const uint8_t *b = s;
  while (n--) *a++ = *b++;
  return d;
}
void *memset(void *d, int c, unsigned n) {
  uint8_t *a = d;
  while (n--) *a++ = (uint8_t)c;
  return d;
}

static inline void irq_off(void) { __asm__ volatile("csrci mstatus, 8"); }
static inline void irq_on(void)  { __asm__ volatile("csrsi mstatus, 8"); }

/* ---- polled transmit --------------------------------------------------- */

static void uart_putc(uint32_t u, uint8_t b) {
  while (UART_TXFIFO_CNT(u) >= UART_TXFIFO_ROOM) {}
  UART_FIFO(u) = b;
}

static void dbg_str(const char *s) { while (*s) uart_putc(UART1, (uint8_t)*s++); }

static void dbg_dec(uint32_t v) {
  char b[10]; unsigned n = 0;
  do { b[n++] = (char)('0' + v % 10u); v /= 10u; } while (v);
  while (n) uart_putc(UART1, (uint8_t)b[--n]);
}

static void dbg_hex(uint32_t v) {
  dbg_str("0x");
  for (int s = 28; s >= 0; s -= 4) uart_putc(UART1, (uint8_t)"0123456789abcdef"[(v >> s) & 15u]);
}

/* ---- watchdogs, clocks, pins ------------------------------------------- */

static void wdt_off(void) {
  for (unsigned g = 0; g < 2; g++) {
    TIMG_WDTWPROTECT(g) = WDT_KEY;
    TIMG_WDTCONFIG0(g) = 0;
    TIMG_WDTWPROTECT(g) = 0;
  }
  RTC_CNTL_WDTWPROTECT = WDT_KEY;
  RTC_CNTL_WDTCONFIG0 = 0;
  RTC_CNTL_WDTWPROTECT = 0;
  RTC_CNTL_SWD_WPROTECT = SWD_KEY;
  RTC_CNTL_SWD_CONF |= 1u << 31;          /* super watchdog: auto-feed */
  RTC_CNTL_SWD_WPROTECT = 0;
}

/* UART0 is left as the ROM set it up (115200 8N1 on GPIO20/21).  UART1:
 * clock on, 115200 from the 40 MHz crystal, pins through the GPIO matrix. */
static void uart1_init(void) {
  SYSTEM_PERIP_CLK_EN0 |= SYSTEM_UART1_BIT;
  SYSTEM_PERIP_RST_EN0 &= ~SYSTEM_UART1_BIT;
  UART_CLK_CONF(UART1) = (3u << 20) | (1u << 22) | (1u << 24) | (1u << 25);
  UART_CLKDIV(UART1) = 347u | (4u << 20);
  GPIO_FUNC_OUT_SEL(EMBER_U1TX_GPIO) = SIG_U1TXD;
  GPIO_ENABLE_W1TS = 1u << EMBER_U1TX_GPIO;
  IO_MUX(EMBER_U1TX_GPIO) = 1u << 12;                   /* function 1: GPIO */
  IO_MUX(EMBER_U1RX_GPIO) = (1u << 12) | (1u << 9) | (1u << 8);   /* GPIO, input, pull-up */
  GPIO_FUNC_IN_SEL(SIG_U1RXD) = (1u << 6) | EMBER_U1RX_GPIO;
}

/* ---- receive interrupt -> ring ----------------------------------------- */

static inline int ring_full(void) {
  return (uint8_t)((rx.head + 1u) & (EMBER_RING_SIZE - 1u)) == rx.tail;
}

/* Move the UART's FIFO into the ring.  When the ring is full the bytes
 * stay in the FIFO and the interrupt is masked until the main loop has
 * made room (rx_resume).  Runs in the ISR, or with interrupts off. */
static void rx_drain(void) {
  while (UART_RXFIFO_CNT(UART0) != 0) {
    if (ring_full()) {
      UART_INT_ENA(UART0) &= ~(UART_INT_RXFIFO_FULL | UART_INT_RXFIFO_TOUT);
      rx_paused = 1;
      return;
    }
    ember_ring_push_isr(&rx, (uint8_t)UART_FIFO(UART0));
  }
}

static void uart0_isr(void) {
  uint32_t st = UART_INT_ST(UART0);
  UART_INT_CLR(UART0) = st;
  if (st & UART_INT_RXFIFO_OVF) rx.overruns++;
  rx_drain();
}

static void rx_resume(void) {
  irq_off();
  rx_paused = 0;
  rx_drain();
  if (!rx_paused) UART_INT_ENA(UART0) |= UART_INT_RXFIFO_FULL | UART_INT_RXFIFO_TOUT;
  irq_on();
}

static void uart0_rx_init(void) {
  /* an interrupt as soon as one byte is there, and after two idle symbols */
  UART_CONF1(UART0) = 1u | (1u << 21);
  UART_MEM_CONF(UART0) = (UART_MEM_CONF(UART0) & ~(0x3FFu << 16)) | (2u << 16);
  UART_INT_CLR(UART0) = 0xFFFFFFFFu;
  UART_INT_ENA(UART0) = UART_INT_RXFIFO_FULL | UART_INT_RXFIFO_TOUT | UART_INT_RXFIFO_OVF;
  INTR_MAP(SRC_UART0) = LINE_UART0;
}

/* ---- tick --------------------------------------------------------------- */

static void systimer_init(void) {
  SYSTEM_PERIP_CLK_EN0 |= SYSTEM_SYSTIMER_BIT;
  SYSTEM_PERIP_RST_EN0 &= ~SYSTEM_SYSTIMER_BIT;
#if EMBER_TICK_HOST
  uint32_t period = SYSTIMER_HZ / 1000u;              /* 1 ms after the request */
#else
  uint32_t period = SYSTIMER_HZ / 1000u * EMBER_TICK_MS;
#endif
  SYSTIMER_CONF = (SYSTIMER_CONF | SYSTIMER_CLK_EN | SYSTIMER_UNIT0_WORK_EN) & ~SYSTIMER_TARGET0_WORK_EN;
  SYSTIMER_TARGET0_CONF = SYSTIMER_PERIOD_MODE | period;
  SYSTIMER_COMP0_LOAD = 1;
  SYSTIMER_INT_CLR = 1;
  SYSTIMER_INT_ENA = 1;
  INTR_MAP(SRC_SYSTIMER_TARGET0) = LINE_SYSTIMER;
#if EMBER_TICK_HOST
  UART_CONF1(UART1) = 1u;
  UART_INT_CLR(UART1) = 0xFFFFFFFFu;
  UART_INT_ENA(UART1) = UART_INT_RXFIFO_FULL;
  INTR_MAP(SRC_UART1) = LINE_UART1;
#else
  SYSTIMER_CONF |= SYSTIMER_TARGET0_WORK_EN;
#endif
}

static void systimer_isr(void) {
  SYSTIMER_INT_CLR = 1;
#if EMBER_TICK_HOST
  if (tick_req == 0) return;
  if (--tick_req == 0) SYSTIMER_CONF &= ~SYSTIMER_TARGET0_WORK_EN;
#endif
  ticks_pending++;
}

#if EMBER_TICK_HOST
static void uart1_isr(void) {
  UART_INT_CLR(UART1) = UART_INT_RXFIFO_FULL;
  while (UART_RXFIFO_CNT(UART1) != 0) {
    if ((uint8_t)UART_FIFO(UART1) != (uint8_t)'t') continue;
    if (tick_req++ == 0) {
      SYSTIMER_COMP0_LOAD = 1;
      SYSTIMER_CONF |= SYSTIMER_TARGET0_WORK_EN;
    }
  }
}
#endif

static void irq_init(void) {
  CPU_INT_TYPE = 0;                                    /* level */
  CPU_INT_PRI(LINE_UART0) = 1;
  CPU_INT_PRI(LINE_UART1) = 1;
  CPU_INT_PRI(LINE_SYSTIMER) = 1;
  CPU_INT_THRESH = 1;
  CPU_INT_ENABLE = (1u << LINE_UART0) | (1u << LINE_UART1) | (1u << LINE_SYSTIMER);
}

/* ---- traps -------------------------------------------------------------- */

static EMBER_NORETURN void halt(void) {
  irq_off();
  for (;;) __asm__ volatile("wfi");
}

void rt_trap(uint32_t cause, uint32_t epc, uint32_t tval) {
  if (cause & 0x80000000u) {
    irq_count++;
    switch (cause & 31u) {
    case LINE_UART0: uart0_isr(); return;
    case LINE_SYSTIMER: systimer_isr(); return;
#if EMBER_TICK_HOST
    case LINE_UART1: uart1_isr(); return;
#endif
    default: break;
    }
  }
  dbg_str("# trap cause="); dbg_dec(cause & 0x7FFFFFFFu);
  if (cause & 0x80000000u) dbg_str(" (interrupt)");
  dbg_str(" pc="); dbg_hex(epc);
  dbg_str(" tval="); dbg_hex(tval);
  dbg_str(" rx="); dbg_dec(n_rx);
  dbg_str(" tick="); dbg_dec(n_tick);
  dbg_str("\n");
  halt();
}

void ember_trap(const char *where) {
  /* a `#` line, as the trap of the CPU above: not a `note` line, which a
   * program's note named `trap` would be */
  dbg_str("# trap "); dbg_str(where);
  dbg_str(" rx="); dbg_dec(n_rx);
  dbg_str(" tick="); dbg_dec(n_tick);
  dbg_str("\n");
  halt();
}

/* ---- what the emitted code calls ---------------------------------------- */

static inline int input_ready(void) {
  return ticks_pending != 0 || rx.head != rx.tail || rx_paused;
}

uint16_t ember_input_next(void) {
  if (ticks_pending != 0) {
    irq_off(); ticks_pending--; irq_on();
    n_tick++;
#if EMBER_TRACE >= 1
    dbg_str("tick\n");
#endif
    return 0x0100u;
  }
  uint16_t v = ember_ring_take(&rx);
  if (v == 0xFFFFu) {
    if (!rx_paused) return v;
    rx_resume();
    v = ember_ring_take(&rx);
    if (v == 0xFFFFu) return v;
  } else if (rx_paused) {
    rx_resume();
  }
  n_rx++;
  return v;
}

uint16_t ember_ring_pop(void) { return ember_input_next(); }

void ember_out_byte(uint8_t b) {
  uart_putc(UART0, b);
  n_tx++; frame_tx++;
}

void ember_out_end(void) {
#if EMBER_TRACE >= 1
  dbg_str("tx "); dbg_dec(frame_tx); dbg_str("\n");
#endif
  frame_tx = 0;
}

void ember_drop(uint8_t code) {
#if EMBER_TRACE >= 2 && APP == APP_STACK
  dbg_str("drop reason=");
  if (code < drop_names_count) dbg_str(drop_names[code]);
  else { dbg_str("code-"); dbg_dec(code); }
  dbg_str("\n");
#else
  (void)code;
#endif
}

void ember_note(uint8_t code, uint32_t value) {
#if EMBER_TRACE >= 2 && APP == APP_STACK
  dbg_str("note ");
  if (code < note_names_count) dbg_str(note_names[code]);
  else { dbg_str("note-"); dbg_dec(code); }
  dbg_str(" "); dbg_dec(value); dbg_str("\n");
#else
  (void)code; (void)value;
#endif
}

uint32_t ember_mmio_read32(uint32_t addr) { return REG(addr); }
void ember_mmio_write32(uint32_t addr, uint32_t value) { REG(addr) = value; }

/* ---- main loops ---------------------------------------------------------- */

#if APP == APP_STACK || APP == APP_ECHO
#if EMBER_ICOUNT
static inline uint32_t instret(void) {
  uint32_t v;
  __asm__ volatile("csrr %0, minstret" : "=r"(v));
  return v;
}
static uint32_t ins_busy, ins_mark;       /* instructions outside idle_line */
#endif

static void idle_line(void) {
#if EMBER_TRACE >= 1
#if EMBER_ICOUNT
  ins_busy += instret() - ins_mark;
  uint32_t ins = ins_busy;
#else
  uint32_t ins = 0;
#endif
  dbg_str("# idle rx="); dbg_dec(n_rx);
  dbg_str(" tick="); dbg_dec(n_tick);
  dbg_str(" tx="); dbg_dec(n_tx);
  dbg_str(" irq="); dbg_dec(irq_count);
  dbg_str(" ovf="); dbg_dec(rx.overruns);
  dbg_str(" ins="); dbg_dec(ins);
  dbg_str("\n");
#if EMBER_ICOUNT
  ins_mark = instret();
#endif
#endif
}

static void step(void) {
#if APP == APP_ECHO
  uint16_t v = ember_input_next();
  if (v < 0x100u) ember_out_byte((uint8_t)v);
#else
  entry();
#endif
}
#endif

void rt_main(void) {
  wdt_off();
#if APP == APP_BOOT
  for (;;) {}
#else
  uart1_init();
#if APP == APP_HELLO
  dbg_str("hello\n");
  halt();
#elif APP == APP_TRAP
  dbg_str("about to trap\n");
  __asm__ volatile(".word 0");                         /* illegal instruction */
  halt();
#else
  uart0_rx_init();
  systimer_init();
  irq_init();
#if EMBER_TRACE >= 1
  dbg_str("# ember-trace v1  impl=esp32c3  build=dev  profile=rv32  link=slip\n");
#endif
  irq_on();
  uint32_t reported = 0;
  for (;;) {
    uint32_t before;
    do { before = n_rx + n_tick; step(); } while (n_rx + n_tick != before);
    if (before != reported) { reported = before; idle_line(); }
    irq_off();
    if (!input_ready()) __asm__ volatile("wfi");       /* a pending interrupt ends it */
    irq_on();
  }
#endif
#endif
}
