# Ember on the Z80 with SDCC (plan M4z).  Run inside nix-shell.
#
#   make OUT=dir NAME=stack PROG=path/to/net.sdcc-z80.c [DEFS="-DEMBER_TRACE=0"] [MMIO=1]
#
# Produces $(OUT)/$(NAME).ihx (ROM image from 0x0000, RAM from 0x8000),
# .map and .noi (symbols).
HERE  := $(dir $(lastword $(MAKEFILE_LIST)))
OUT  ?= $(HERE)../../.lake/build/z80
NAME ?= stack
PROG ?=
DEFS ?=
MMIO ?=

# warnings 110/126 ("unreachable code") stay errors: SDCC 4.6 gives them when
# it deletes live code (docs/Ember-plan.md, decision log), and the stack has none.
# --max-allocs-per-node 10000 (SDCC's default 3000): the register allocator
# searches further.  Validated for SDCC 4.6.0 #16555 only; with 30000 and
# 100000 that version miscompiles the stack.  Revalidate on any other SDCC
# (decision log, 2026-10-23).  Ember/Tools/Z80.lean (sdccFlags) and
# Tests/Ember/LangTests.lean (sdcc) pass the same.
ALLOCS := --max-allocs-per-node 10000
CFLAGS := -mz80 --std-c99 --opt-code-size $(ALLOCS) --Werror \
          -I$(HERE)../common $(DEFS)
RELS := $(OUT)/$(NAME).crt0.rel $(OUT)/$(NAME).rt.rel $(OUT)/$(NAME).prog.rel $(if $(MMIO),$(OUT)/$(NAME).mmio.rel)

all: $(OUT)/$(NAME).ihx

$(OUT)/$(NAME).crt0.rel: $(HERE)crt0.s
	@mkdir -p $(OUT)
	sdasz80 -g -o $@ $<
$(OUT)/$(NAME).rt.rel: $(HERE)rt.c $(HERE)../common/ember_rt.h FORCE
	@mkdir -p $(OUT)
	sdcc $(CFLAGS) -c $< -o $@
$(OUT)/$(NAME).mmio.rel: $(HERE)mmio.c FORCE
	sdcc $(CFLAGS) -c $< -o $@
$(OUT)/$(NAME).prog.rel: $(PROG) FORCE
	sdcc $(CFLAGS) -c $< -o $@
$(OUT)/$(NAME).ihx: $(RELS)
	sdcc -mz80 --no-std-crt0 --code-loc 0x0100 --data-loc 0x8000 -Wl-j $(RELS) -o $@
	@grep -q '^DEF _rt_rx_buf 0x..00$$' $(OUT)/$(NAME).noi || { echo "the receive ring is not on a page boundary"; rm -f $@; exit 1; }

FORCE:
.PHONY: all FORCE
