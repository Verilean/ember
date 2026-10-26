# Ember on the ESP32-C3 (plan M4).  Run inside nix-shell.
#
#   make OUT=dir NAME=stack PROG=path/to/net.rv32.c [DEFS="-DEMBER_TICK_HOST=1"]
#   make OUT=dir NAME=echo  DEFS="-DAPP=APP_ECHO"
#
# Produces $(OUT)/$(NAME).elf, .map and .bin; the .bin is a 4 MB flash
# image with the program at offset 0, where the ROM boot loader looks
# for it: `qemu -drive file=NAME.bin,if=mtd,format=raw`, or on a board
# `esptool --chip esp32c3 write-flash 0x0 NAME.img`.
HERE  := $(dir $(lastword $(MAKEFILE_LIST)))
CROSS ?= riscv32-none-elf-
OUT   ?= $(HERE)../../.lake/build/esp32c3
NAME  ?= stack
PROG  ?=
DEFS  ?=

CFLAGS := -march=rv32imc_zicsr -mabi=ilp32 -Os -std=c99 -ffreestanding -fno-builtin \
          -ffunction-sections -fdata-sections -Wall -Wextra -Werror -Wno-unused-function \
          -I$(HERE)../common -I$(HERE) $(DEFS)
LDFLAGS := -march=rv32imc_zicsr -mabi=ilp32 -nostdlib -nostartfiles -T $(HERE)link.ld \
           -Wl,--gc-sections -Wl,-Map,$(OUT)/$(NAME).map -Wl,--no-warn-rwx-segments

OBJS := $(OUT)/$(NAME).start.o $(OUT)/$(NAME).rt.o $(if $(PROG),$(OUT)/$(NAME).prog.o)

all: $(OUT)/$(NAME).bin

$(OUT)/$(NAME).start.o: $(HERE)start.S
	@mkdir -p $(OUT)
	$(CROSS)gcc $(CFLAGS) -c $< -o $@
$(OUT)/$(NAME).rt.o: $(HERE)rt.c $(HERE)soc.h $(HERE)../common/ember_rt.h $(HERE)../common/ring.h FORCE
	@mkdir -p $(OUT)
	$(CROSS)gcc $(CFLAGS) -c $< -o $@
$(OUT)/$(NAME).prog.o: $(PROG) FORCE
	$(CROSS)gcc $(CFLAGS) -c $< -o $@
$(OUT)/$(NAME).elf: $(OBJS) $(HERE)link.ld
	$(CROSS)gcc $(LDFLAGS) $(OBJS) -lgcc -o $@
$(OUT)/$(NAME).bin: $(OUT)/$(NAME).elf
	esptool --chip esp32c3 elf2image --flash-mode dio --flash-freq 40m --flash-size 4MB -o $(OUT)/$(NAME).img $< >/dev/null
	cp $(OUT)/$(NAME).img $@ && truncate -s 4M $@

FORCE:
.PHONY: all FORCE
