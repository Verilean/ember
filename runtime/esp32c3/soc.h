/* ESP32-C3 registers used by the Ember runtime (ESP32-C3 Technical
 * Reference Manual; the same offsets as Espressif's QEMU models). */
#ifndef EMBER_ESP32C3_SOC_H
#define EMBER_ESP32C3_SOC_H

#include <stdint.h>

#define REG(a) (*(volatile uint32_t *)(uintptr_t)(a))

/* UART0 (SLIP) and UART1 (trace) */
#define UART0 0x60000000u
#define UART1 0x60010000u
#define UART_FIFO(u)     REG((u) + 0x00)
#define UART_INT_RAW(u)  REG((u) + 0x04)
#define UART_INT_ST(u)   REG((u) + 0x08)
#define UART_INT_ENA(u)  REG((u) + 0x0C)
#define UART_INT_CLR(u)  REG((u) + 0x10)
#define UART_CLKDIV(u)   REG((u) + 0x14)
#define UART_STATUS(u)   REG((u) + 0x1C)
#define UART_CONF0(u)    REG((u) + 0x20)
#define UART_CONF1(u)    REG((u) + 0x24)
#define UART_MEM_CONF(u) REG((u) + 0x60)
#define UART_CLK_CONF(u) REG((u) + 0x78)
#define UART_INT_RXFIFO_FULL 0x001u
#define UART_INT_RXFIFO_OVF  0x010u
#define UART_INT_RXFIFO_TOUT 0x100u
#define UART_RXFIFO_CNT(u) (UART_STATUS(u) & 0x3FFu)
#define UART_TXFIFO_CNT(u) ((UART_STATUS(u) >> 16) & 0x3FFu)
#define UART_TXFIFO_ROOM 120u       /* of 128 */

/* GPIO matrix and pads (UART1 has no default pins) */
#define GPIO_ENABLE_W1TS       REG(0x60004024u)
#define GPIO_FUNC_IN_SEL(sig)  REG(0x60004154u + 4u * (sig))
#define GPIO_FUNC_OUT_SEL(pin) REG(0x60004554u + 4u * (pin))
#define IO_MUX(pin)            REG(0x60009004u + 4u * (pin))
#define SIG_U1RXD 9u
#define SIG_U1TXD 9u

/* Watchdogs */
#define RTC_CNTL_WDTCONFIG0   REG(0x60008090u)
#define RTC_CNTL_WDTWPROTECT  REG(0x600080A8u)
#define RTC_CNTL_SWD_CONF     REG(0x600080ACu)
#define RTC_CNTL_SWD_WPROTECT REG(0x600080B0u)
#define TIMG_WDTCONFIG0(g)    REG(0x6001F048u + 0x1000u * (g))
#define TIMG_WDTWPROTECT(g)   REG(0x6001F064u + 0x1000u * (g))
#define WDT_KEY 0x50D83AA1u
#define SWD_KEY 0x8F1D312Au

/* Clock gates */
#define SYSTEM_PERIP_CLK_EN0 REG(0x600C0010u)
#define SYSTEM_PERIP_RST_EN0 REG(0x600C0018u)
#define SYSTEM_UART1_BIT (1u << 5)
#define SYSTEM_SYSTIMER_BIT (1u << 29)

/* Interrupt matrix: peripheral source -> CPU interrupt line */
#define INTR_MAP(src)      REG(0x600C2000u + 4u * (src))
#define CPU_INT_ENABLE     REG(0x600C2104u)
#define CPU_INT_TYPE       REG(0x600C2108u)
#define CPU_INT_CLEAR      REG(0x600C210Cu)
#define CPU_INT_PRI(line)  REG(0x600C2114u + 4u * (line))
#define CPU_INT_THRESH     REG(0x600C2194u)
#define SRC_UART0 21u
#define SRC_UART1 22u
#define SRC_SYSTIMER_TARGET0 37u

/* SYSTIMER: unit 0 counts at 16 MHz, comparator 0 gives the tick */
#define SYSTIMER_CONF         REG(0x60023000u)
#define SYSTIMER_TARGET0_CONF REG(0x60023034u)
#define SYSTIMER_COMP0_LOAD   REG(0x60023050u)
#define SYSTIMER_INT_ENA      REG(0x60023064u)
#define SYSTIMER_INT_CLR      REG(0x6002306Cu)
#define SYSTIMER_CLK_EN          (1u << 31)
#define SYSTIMER_UNIT0_WORK_EN   (1u << 30)
#define SYSTIMER_TARGET0_WORK_EN (1u << 24)
#define SYSTIMER_PERIOD_MODE     (1u << 30)
#define SYSTIMER_HZ 16000000u

#endif
