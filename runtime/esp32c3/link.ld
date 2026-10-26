/* Ember on the ESP32-C3, loaded into RAM by the ROM boot loader.
 *
 * Internal SRAM1 appears twice: on the instruction bus from 0x40380000
 * and on the data bus from 0x3FC80000 (the same bytes).  Code takes the
 * first 64 KB, data the next 64 KB; the ROM's own data and stack are at
 * the top of the RAM (above 0x3FCD0000) and are left alone. */
ENTRY(_start)

MEMORY {
  iram (rx)  : ORIGIN = 0x40380000, LENGTH = 64K
  dram (rw)  : ORIGIN = 0x3FC90000, LENGTH = 64K
}

SECTIONS {
  .text : {
    KEEP(*(.text.entry))
    . = ALIGN(256);
    KEEP(*(.text.vectors))
    *(.text .text.*)
    . = ALIGN(4);
    _etext = .;
  } > iram

  .rodata : {
    *(.rodata .rodata.* .srodata .srodata.*)
    . = ALIGN(4);
  } > dram

  .data : {
    __global_pointer$ = . + 0x800;
    *(.data .data.* .sdata .sdata.*)
    . = ALIGN(4);
  } > dram

  .bss (NOLOAD) : {
    _bss_start = .;
    *(.bss .bss.* .sbss .sbss.* COMMON)
    . = ALIGN(4);
    _bss_end = .;
  } > dram

  .stack (NOLOAD) : {
    . = ALIGN(16);
    _stack_bottom = .;
    . += 4096;
    _stack_top = .;
  } > dram

  /DISCARD/ : { *(.comment) *(.riscv.attributes) *(.note.*) *(.eh_frame) }
}
