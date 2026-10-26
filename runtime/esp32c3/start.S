/* Ember on the ESP32-C3: reset entry and trap entry (plan M4.1).
 *
 * The ROM boot loader has copied the image's segments into RAM and jumps
 * to _start in machine mode.  The C3 takes every exception and interrupt
 * through a vector table of jumps; all 32 entries go to one handler,
 * which saves the caller-saved registers and calls rt_trap. */
        .option norvc
        .section .text.entry, "ax"
        .globl _start
_start:
        csrci   mstatus, 8              /* interrupts off */
        .option push
        .option norelax
        la      gp, __global_pointer$
        .option pop
        la      sp, _stack_top
        la      t0, _vectors
        ori     t0, t0, 1               /* vectored */
        csrw    mtvec, t0
        la      t0, _bss_start
        la      t1, _bss_end
1:      bgeu    t0, t1, 2f
        sw      zero, 0(t0)
        addi    t0, t0, 4
        j       1b
2:      call    rt_main
3:      j       3b

        .section .text.vectors, "ax"
        .balign 256
        .globl _vectors
_vectors:
        .rept 32
        j       _trap_entry
        .endr

        .section .text, "ax"
        .balign 4
_trap_entry:
        addi    sp, sp, -64
        sw      ra,  0(sp)
        sw      t0,  4(sp)
        sw      t1,  8(sp)
        sw      t2, 12(sp)
        sw      a0, 16(sp)
        sw      a1, 20(sp)
        sw      a2, 24(sp)
        sw      a3, 28(sp)
        sw      a4, 32(sp)
        sw      a5, 36(sp)
        sw      a6, 40(sp)
        sw      a7, 44(sp)
        sw      t3, 48(sp)
        sw      t4, 52(sp)
        sw      t5, 56(sp)
        sw      t6, 60(sp)
        csrr    a0, mcause
        csrr    a1, mepc
        csrr    a2, mtval
        call    rt_trap
        lw      ra,  0(sp)
        lw      t0,  4(sp)
        lw      t1,  8(sp)
        lw      t2, 12(sp)
        lw      a0, 16(sp)
        lw      a1, 20(sp)
        lw      a2, 24(sp)
        lw      a3, 28(sp)
        lw      a4, 32(sp)
        lw      a5, 36(sp)
        lw      a6, 40(sp)
        lw      a7, 44(sp)
        lw      t3, 48(sp)
        lw      t4, 52(sp)
        lw      t5, 56(sp)
        lw      t6, 60(sp)
        addi    sp, sp, 64
        mret
