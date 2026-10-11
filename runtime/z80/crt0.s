;; Ember on the Z80: reset, start-up and the interrupt routine (plan M4z.2).
;;
;; ROM from 0x0000, RAM from 0x8000 (an RC2014-class board).  Interrupt
;; mode 1: every interrupt comes to 0x0038.  sdcc's library start-up is
;; not used (`--no-std-crt0`).
;;
;; The receive ring (design §2.2) lives here: the interrupt routine is
;; its only producer, `ember_input_next` in rt.c its only consumer.  It
;; is written in assembly because at 115 200 baud a byte arrives every
;; 640 T-states: this routine takes about 285.
        .module crt0
        .globl  _main

ACIA_CTRL  = 0x80
ACIA_DATA  = 0x81
TICK       = 0xC1
ACIA_HOLD  = 0xD6               ; RTS high, receive interrupt on
RING_HIGH  = 224                ; fill at which RTS goes high
        .globl  l__DATA
        .globl  s__DATA
        .globl  l__INITIALIZER
        .globl  s__INITIALIZER
        .globl  s__INITIALIZED

        .area   _HEADER (ABS)
        .org    0x0000
        di
        jp      init

        .org    0x0038
        jp      isr

        ;; the order of the areas in the image
        .area   _HOME
        .area   _CODE
        .area   _INITIALIZER
        .area   _GSINIT
        .area   _GSFINAL
        .area   _DATA
        .area   _INITIALIZED
        .area   _BSEG
        .area   _BSS
        .area   _HEAP

        ;; The ring.  This module is linked first, so the buffer starts
        ;; at the first byte of RAM: a page boundary, which is what lets
        ;; the head be used as the low byte of an address (the Makefile
        ;; checks it).
        .area   _DATA
_rt_rx_buf::
        .ds     256
_rt_rx_head::                   ; written by the interrupt routine only
        .ds     1
_rt_rx_tail::                   ; written by the main loop only; must follow head
        .ds     1
_rt_rx_overruns::               ; bytes lost: ring full, or ACIA overrun
        .ds     2
_rt_rx_held::                   ; non-zero while RTS is high
        .ds     1
_rt_ticks_pending::
        .ds     1

        .area   _CODE
isr:
        push    af
        push    hl
        in      a, (ACIA_CTRL)
        rrca                            ; RDRF
        jr      NC, 4$
        and     #0x10                   ; OVRN (bit 5 before the rotate)
        jr      Z, 1$
        ld      hl, (_rt_rx_overruns)
        inc     hl
        ld      (_rt_rx_overruns), hl
1$:     ld      hl, (_rt_rx_head)       ; l = head, h = tail
        ld      a, l
        inc     a
        cp      h
        jr      Z, 3$                   ; full
        ld      h, #>_rt_rx_buf
        in      a, (ACIA_DATA)          ; reading clears RDRF and the interrupt
        ld      (hl), a
        inc     l
        ld      a, l
        ld      (_rt_rx_head), a
        ld      hl, #_rt_rx_tail
        sub     a, (hl)                 ; fill
        cp      #RING_HIGH
        jr      C, 4$
        ld      a, #ACIA_HOLD           ; nearly full: ask the sender to wait
        out     (ACIA_CTRL), a
        ld      (_rt_rx_held), a
        jr      4$
3$:     in      a, (ACIA_DATA)          ; full: the byte is lost
        ld      hl, (_rt_rx_overruns)
        inc     hl
        ld      (_rt_rx_overruns), hl
4$:     in      a, (TICK)               ; reading clears a pending tick
        rrca
        jr      NC, 5$
        ld      hl, #_rt_ticks_pending
        inc     (hl)
5$:     pop     hl
        pop     af
        ei                              ; takes effect after the reti
        reti

init:
        ld      sp, #0x0000     ; the stack grows down from the top of RAM
        im      1
        ;; C wants its zero-initialised variables zero: RAM is not
        ld      hl, #s__DATA
        ld      bc, #l__DATA
1$:     ld      a, b
        or      a, c
        jr      Z, 2$
        ld      (hl), #0
        inc     hl
        dec     bc
        jr      1$
2$:     call    gsinit
        call    _main
3$:     di
        halt
        jr      3$

        .area   _GSINIT
gsinit::
        ;; initialised variables: their values are in ROM
        ld      bc, #l__INITIALIZER
        ld      a, b
        or      a, c
        jr      Z, 4$
        ld      de, #s__INITIALIZED
        ld      hl, #s__INITIALIZER
        ldir
4$:
        .area   _GSFINAL
        ret
