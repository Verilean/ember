import Ember.Z80.Asm

/-!
# Ember.Z80.Runtime — the routines generated code calls (plan M6.6)

Hand-written Z80 assembly, in pieces; a program gets the pieces it
refers to (and what those refer to).  Conventions:

* 8-bit values are in `A`, 16-bit values in `HL`;
* 32- and 64-bit values are in memory, in the accumulator `rt_acc`
  (8 bytes, little-endian); a second operand is the memory `HL` points
  to.  These routines may change every register;
* a shift count is in `B` (any value: 0 leaves the operand, a count of
  the width or more gives 0);
* division by zero gives 0, as does the remainder (Ember's semantics);
* `rt_bound` keeps `A`, `DE` and `HL`.

Each routine is tested against its specification on the Z80 model
(`ember-z80 rt-check`): exhaustively for 8-bit operands, on random and
edge values otherwise.
-/

namespace Ember.Z80.Runtime
open Ember.Z80.Asm

/-- A piece of assembly; the labels it defines are found by parsing. -/
structure Piece where
  src : String := ""
  /-- Data that the text syntax has no notation for (strings). -/
  items : List Item := []

/-- The 32/64-bit operations that are one loop over the bytes. -/
def bytewise (name op : String) (carry : Bool) : Piece := ⟨s!"
rt_{name}64: ld b,8
  jr rt_{name}w
rt_{name}32: ld b,4
rt_{name}w: ld de,rt_acc
{if carry then "  or a" else ""}
rt_{name}w_l: ld a,(de)
  {op} (hl)
  ld (de),a
  inc hl
  inc de
  djnz rt_{name}w_l
  ret
", []⟩

def pieces : List Piece := [
  -- accumulator := (HL)
  ⟨"
rt_ld64: ld bc,8
  jr rt_ldw
rt_ld32: ld bc,4
rt_ldw: ld de,rt_acc
  ldir
  ret
", []⟩,
  -- (HL) := accumulator
  ⟨"
rt_st64: ld bc,8
  jr rt_stw
rt_st32: ld bc,4
rt_stw: ex de,hl
  ld hl,rt_acc
  ldir
  ret
", []⟩,
  bytewise "add" "adc a," true,
  bytewise "sub" "sbc a," true,
  bytewise "and" "and" false,
  bytewise "or" "or" false,
  bytewise "xor" "xor" false,
  -- flags of accumulator − (HL): Z when equal, C when below
  ⟨"
rt_cmp64: ld b,8
  jr rt_cmpw
rt_cmp32: ld b,4
rt_cmpw: ld de,rt_acc
  ld c,0
  or a
rt_cmpw_l: ld a,(de)
  sbc a,(hl)
  push af
  or c
  ld c,a
  pop af
  inc hl
  inc de
  djnz rt_cmpw_l
  inc c
  dec c
  ret
", []⟩,
  ⟨"
rt_not64: ld b,8
  jr rt_notw
rt_not32: ld b,4
rt_notw: ld hl,rt_acc
rt_notw_l: ld a,(hl)
  cpl
  ld (hl),a
  inc hl
  djnz rt_notw_l
  ret
", []⟩,
  ⟨"
rt_neg64: ld b,8
  jr rt_negw
rt_neg32: ld b,4
rt_negw: ld hl,rt_acc
  or a
rt_negw_l: ld a,0
  sbc a,(hl)
  ld (hl),a
  inc hl
  djnz rt_negw_l
  ret
", []⟩,
  -- accumulator shifted left by B
  ⟨"
rt_shl64: ld c,8
  jr rt_shlw
rt_shl32: ld c,4
rt_shlw: inc b
  dec b
  ret z
rt_shlw_o: push bc
  ld b,c
  ld hl,rt_acc
  or a
rt_shlw_i: rl (hl)
  inc hl
  djnz rt_shlw_i
  pop bc
  djnz rt_shlw_o
  ret
", []⟩,
  ⟨"
rt_shr64: ld c,8
  jr rt_shrw
rt_shr32: ld c,4
rt_shrw: inc b
  dec b
  ret z
rt_shrw_o: push bc
  ld b,c
  ld hl,rt_acc
  ld e,c
  ld d,0
  add hl,de
  or a
rt_shrw_i: dec hl
  rr (hl)
  djnz rt_shrw_i
  pop bc
  djnz rt_shrw_o
  ret
", []⟩,
  -- accumulator := A, := HL, zero-extended; rt_zx32: clear its upper half
  ⟨"
rt_acc_a: ld l,a
  ld h,0
rt_acc_hl: ld (rt_acc),hl
  ld hl,0
  ld (rt_acc+2),hl
rt_zx32: ld hl,0
  ld (rt_acc+4),hl
  ld (rt_acc+6),hl
  ret
", []⟩,
  -- a shift count from a wide value: A := 255 when it does not fit a byte
  ⟨"
rt_sat64: ld b,7
  jr rt_satw
rt_sat32: ld b,3
rt_satw: ld hl,rt_acc+1
  xor a
rt_satw_l: or (hl)
  inc hl
  djnz rt_satw_l
  jr nz,rt_satw_big
  ld a,(rt_acc)
  ret
rt_satw_big: ld a,255
  ret
", []⟩,
  ⟨"
rt_sat16: ld a,h
  or a
  ld a,l
  ret z
  ld a,255
  ret
", []⟩,
  -- accumulator := accumulator * (HL)
  ⟨"
rt_mul64: ld a,8
  jr rt_mulw
rt_mul32: ld a,4
rt_mulw: ld (rt_n),a
  ld c,a
  ld b,0
  push bc
  ld de,rt_t1
  ldir
  pop bc
  push bc
  ld hl,rt_acc
  ld de,rt_t2
  ldir
  pop bc
  ld hl,rt_acc
  ld b,c
rt_mulw_z: ld (hl),0
  inc hl
  djnz rt_mulw_z
  ld a,c
  add a,a
  add a,a
  add a,a
rt_mulw_l: push af
  ld a,(rt_n)
  ld b,a
  ld hl,rt_t2
  ld e,a
  ld d,0
  add hl,de
  or a
rt_mulw_r: dec hl
  rr (hl)
  djnz rt_mulw_r
  jr nc,rt_mulw_s
  ld a,(rt_n)
  ld b,a
  ld hl,rt_t1
  ld de,rt_acc
  or a
rt_mulw_a: ld a,(de)
  adc a,(hl)
  ld (de),a
  inc hl
  inc de
  djnz rt_mulw_a
rt_mulw_s: ld a,(rt_n)
  ld b,a
  ld hl,rt_t1
  or a
rt_mulw_h: rl (hl)
  inc hl
  djnz rt_mulw_h
  pop af
  dec a
  jr nz,rt_mulw_l
  ret
", []⟩,
  -- accumulator := accumulator / (HL), remainder in rt_t2; both 0 for a zero divisor
  ⟨"
rt_div64: ld a,8
  jr rt_divw
rt_div32: ld a,4
rt_divw: ld (rt_n),a
  ld c,a
  ld b,0
  ld de,rt_t1
  ldir
  ld a,(rt_n)
  ld b,a
  ld hl,rt_t1
  ld de,rt_t2
  ld c,0
rt_divw_i: ld a,(hl)
  or c
  ld c,a
  xor a
  ld (de),a
  inc hl
  inc de
  djnz rt_divw_i
  ld a,c
  or a
  jr nz,rt_divw_go
  ld a,(rt_n)
  ld b,a
  ld hl,rt_acc
rt_divw_z: ld (hl),0
  inc hl
  djnz rt_divw_z
  ret
rt_divw_go: ld a,(rt_n)
  add a,a
  add a,a
  add a,a
rt_divw_l: push af
  ld a,(rt_n)
  ld b,a
  ld hl,rt_acc
  or a
rt_divw_s1: rl (hl)
  inc hl
  djnz rt_divw_s1
  ld a,(rt_n)
  ld b,a
  ld hl,rt_t2
rt_divw_s2: rl (hl)
  inc hl
  djnz rt_divw_s2
  jr c,rt_divw_sub
  ld a,(rt_n)
  ld b,a
  ld hl,rt_t1
  ld de,rt_t2
  or a
rt_divw_c: ld a,(de)
  sbc a,(hl)
  inc hl
  inc de
  djnz rt_divw_c
  jr c,rt_divw_n
rt_divw_sub: ld a,(rt_n)
  ld b,a
  ld hl,rt_t1
  ld de,rt_t2
  or a
rt_divw_d: ld a,(de)
  sbc a,(hl)
  ld (de),a
  inc hl
  inc de
  djnz rt_divw_d
  ld hl,rt_acc
  inc (hl)
rt_divw_n: pop af
  dec a
  jr nz,rt_divw_l
  ret
", []⟩,
  ⟨"
rt_mod64: ld a,8
  jr rt_modw
rt_mod32: ld a,4
rt_modw: call rt_divw
  ld a,(rt_n)
  ld c,a
  ld b,0
  ld hl,rt_t2
  ld de,rt_acc
  ldir
  ret
", []⟩,
  -- 16 bits: HL := HL op DE
  ⟨"
rt_and16: ld a,h
  and d
  ld h,a
  ld a,l
  and e
  ld l,a
  ret
", []⟩,
  ⟨"
rt_or16: ld a,h
  or d
  ld h,a
  ld a,l
  or e
  ld l,a
  ret
", []⟩,
  ⟨"
rt_xor16: ld a,h
  xor d
  ld h,a
  ld a,l
  xor e
  ld l,a
  ret
", []⟩,
  ⟨"
rt_not16: ld a,h
  cpl
  ld h,a
  ld a,l
  cpl
  ld l,a
  ret
", []⟩,
  ⟨"
rt_neg16: xor a
  sub l
  ld l,a
  sbc a,a
  sub h
  ld h,a
  ret
", []⟩,
  ⟨"
rt_mul16: ld b,h
  ld c,l
  ld hl,0
  ld a,16
rt_mul16_l: add hl,hl
  ex de,hl
  add hl,hl
  ex de,hl
  jr nc,rt_mul16_s
  add hl,bc
rt_mul16_s: dec a
  jr nz,rt_mul16_l
  ret
", []⟩,
  -- HL := HL mod DE, quotient in A (high) and C (low); both 0 for DE = 0
  ⟨"
rt_mod16: ld a,d
  or e
  jr z,rt_mod16_z
  ld a,h
  ld c,l
  ld hl,0
  ld b,16
rt_mod16_l: sla c
  rla
  adc hl,hl
  jr c,rt_mod16_o
  sbc hl,de
  jr nc,rt_mod16_b
  add hl,de
  jr rt_mod16_n
rt_mod16_o: or a
  sbc hl,de
rt_mod16_b: inc c
rt_mod16_n: djnz rt_mod16_l
  ret
rt_mod16_z: ld hl,0
  xor a
  ld c,a
  ret
", []⟩,
  ⟨"
rt_div16: call rt_mod16
  ld h,a
  ld l,c
  ret
", []⟩,
  ⟨"
rt_shl16: inc b
  dec b
  ret z
rt_shl16_l: add hl,hl
  djnz rt_shl16_l
  ret
", []⟩,
  ⟨"
rt_shr16: inc b
  dec b
  ret z
rt_shr16_l: srl h
  rr l
  djnz rt_shr16_l
  ret
", []⟩,
  -- 8 bits: A := A op E
  ⟨"
rt_mul8: ld d,a
  xor a
  ld b,8
rt_mul8_l: add a,a
  rl e
  jr nc,rt_mul8_s
  add a,d
rt_mul8_s: djnz rt_mul8_l
  ret
", []⟩,
  -- A := A mod E, quotient in C; both 0 for E = 0
  ⟨"
rt_mod8: ld c,a
  ld a,e
  or a
  jr z,rt_mod8_z
  xor a
  ld b,8
rt_mod8_l: sla c
  rla
  jr c,rt_mod8_o
  cp e
  jr c,rt_mod8_n
rt_mod8_o: sub e
  inc c
rt_mod8_n: djnz rt_mod8_l
  ret
rt_mod8_z: xor a
  ld c,a
  ret
", []⟩,
  ⟨"
rt_div8: call rt_mod8
  ld a,c
  ret
", []⟩,
  ⟨"
rt_shl8: inc b
  dec b
  ret z
rt_shl8_l: add a,a
  djnz rt_shl8_l
  ret
", []⟩,
  ⟨"
rt_shr8: inc b
  dec b
  ret z
rt_shr8_l: srl a
  djnz rt_shr8_l
  ret
", []⟩,
  -- trap unless HL < BC
  ⟨"
rt_bound: or a
  sbc hl,bc
  add hl,bc
  ret c
  jp rt_trap
", []⟩,
  -- BC (> 0) bytes of zero from HL
  ⟨"
rt_zero: ld (hl),0
  dec bc
  ld a,b
  or c
  ret z
  ld d,h
  ld e,l
  inc de
  ldir
  ret
", []⟩,
  -- `mmio.read32`/`mmio.write32` without devices: a table of 8 addresses
  -- that remembers what was written
  ⟨"
rt_mmio_addr: ld hl,rt_acc
  ld de,rt_ma
  ld bc,4
  ldir
  ret
rt_mmio_find: ld a,(rt_mn)
  ld c,a
  ld hl,rt_mt
rt_mmio_f_l: ld a,c
  or a
  jr z,rt_mmio_f_none
  push hl
  ld de,rt_ma
  ld b,4
rt_mmio_f_c: ld a,(de)
  cp (hl)
  jr nz,rt_mmio_f_ne
  inc hl
  inc de
  djnz rt_mmio_f_c
  pop de
  or a
  ret
rt_mmio_f_ne: pop hl
  ld de,8
  add hl,de
  dec c
  jr rt_mmio_f_l
rt_mmio_f_none: scf
  ret
rt_mmio_read: call rt_mmio_addr
  call rt_mmio_find
  jp nc,rt_ld32
  ld hl,0
  ld (rt_acc),hl
  ld (rt_acc+2),hl
  ret
rt_mmio_write: call rt_mmio_find
  jp nc,rt_st32
  ld a,(rt_mn)
  cp 8
  ret nc
  inc a
  ld (rt_mn),a
  ex de,hl
  ld hl,rt_ma
  ld bc,4
  ldir
  ex de,hl
  jp rt_st32
", []⟩]

/-- The test harness (as `runtime/z80/harness.c`): effects are ports of
the model, the entry is called while input remains and until three calls
in a row consume nothing — whether a call consumed anything is asked of
the model (port `0xD9`: has the position in the input moved?), as the
interpreter's driver compares the position before and after. -/
def harness : List Piece := [
  ⟨"
rt_start: di
  ld sp,0
  call rt_init
rt_main: in a,(0xD0)
  or a
  jr z,rt_done
  ld a,(rt_idle)
  cp 3
  jr nc,rt_done
  call f_entry
  in a,(0xD9)
  or a
  jr nz,rt_main_r
  ld hl,rt_idle
  inc (hl)
  jr rt_main
rt_main_r: xor a
  ld (rt_idle),a
  jr rt_main
rt_done: di
  halt
  jr rt_done
", []⟩,
  ⟨"
rt_input: in a,(0xD1)
  cp 2
  jr z,rt_input_none
  cp 1
  jr z,rt_input_tick
  in a,(0xD2)
  ld l,a
  ld h,0
  ret
rt_input_tick: ld hl,0x0100
  ret
rt_input_none: ld hl,0xFFFF
  ret
", []⟩,
  ⟨"
rt_out_byte: out (0xD3),a
  ret
", []⟩,
  ⟨"
rt_out_end: out (0xD4),a
  ret
", []⟩,
  ⟨"
rt_drop: out (0xD5),a
  ret
", []⟩,
  ⟨"
rt_note: out (0xD6),a
  ret
", []⟩,
  ⟨"
rt_trap: out (0xD7),a
rt_trap_l: di
  halt
  jr rt_trap_l
", []⟩]


/-! ## A board: 68B50 ACIA, interrupt mode 1 (as `runtime/z80`) -/

/-- The fixed cells of the board runtime, from `base` (a page boundary:
the ring's index is the low byte of its address), and their size. -/
def boardCells (base : Nat) : List Item × Nat :=
  ([.equ "rt_rx_buf" base, .equ "rt_rx_head" (base + 256), .equ "rt_rx_tail" (base + 257),
    .equ "rt_rx_overruns" (base + 258), .equ "rt_rx_held" (base + 260), .equ "rt_ticks" (base + 261),
    .equ "rt_frame_tx" (base + 262)], 264)

/-- Reset and interrupt vectors. -/
def boardHead (base : Nat) : List Item :=
  (boardCells base).1 ++
  [.ins { op := .di }, .ins { op := .jp, args := [.imm (.sym "rt_start")] }, .ds 0x34,
   .ins { op := .jp, args := [.imm (.sym "rt_isr")] }]

def cstr (name text : String) : List Item :=
  [.label name, .db ((text.toUTF8.toList.map fun b => Val.num (Int.ofNat b.toNat)) ++ [.num 0])]

/-- A table of names: `name` holds the addresses of the strings. -/
def nameTable (name : String) (xs : List String) : List Item :=
  let labels := (List.range xs.length).map fun k => s!"{name}_{k}"
  [.label name, .dw (labels.map fun l => Val.sym l)] ++
  (labels.zip xs).flatMap fun (l, x) => cstr l x

/-- Start-up, the receive interrupt with its ring and RTS flow control,
the effects; `trace` as `EMBER_TRACE` (0 nothing, 1 `tx N`, 2 also
`drop` and `note`).  `page` is the high byte of the ring's address. -/
def board (trace : Nat) (drops notes : List String) (page : Nat := 0x80) : List Piece := [
  ⟨"
rt_start: ld sp,0
  im 1
  call rt_init
  ld a,0x03
  out (0x80),a
  ld a,0x96
  out (0x80),a
  ei
rt_main: xor a
  ld (rt_consumed),a
  call f_entry
  ld a,(rt_consumed)
  or a
  jr nz,rt_main
  di
  ld a,(rt_ticks)
  or a
  jr nz,rt_main_e
  ld hl,(rt_rx_head)
  ld a,l
  cp h
  jr nz,rt_main_e
  ei
  halt
  jr rt_main
rt_main_e: ei
  jr rt_main
", []⟩,
  ⟨s!"
rt_isr: push af
  push hl
  in a,(0x80)
  rrca
  jr nc,rt_isr_t
  and 0x10
  jr z,rt_isr_r
  ld hl,(rt_rx_overruns)
  inc hl
  ld (rt_rx_overruns),hl
rt_isr_r: ld hl,(rt_rx_head)
  ld a,l
  inc a
  cp h
  jr z,rt_isr_full
  ld h,{page}
  in a,(0x81)
  ld (hl),a
  inc l
  ld a,l
  ld (rt_rx_head),a
  ld hl,rt_rx_tail
  sub (hl)
  cp 224
  jr c,rt_isr_t
  ld a,0xD6
  out (0x80),a
  ld (rt_rx_held),a
  jr rt_isr_t
rt_isr_full: in a,(0x81)
  ld hl,(rt_rx_overruns)
  inc hl
  ld (rt_rx_overruns),hl
rt_isr_t: in a,(0xC1)
  rrca
  jr nc,rt_isr_e
  ld hl,rt_ticks
  inc (hl)
rt_isr_e: pop hl
  pop af
  ei
  reti
", []⟩,
  ⟨s!"
rt_input: ld a,(rt_ticks)
  or a
  jr z,rt_input_b
  di
  ld hl,rt_ticks
  dec (hl)
  ei
  ld a,1
  ld (rt_consumed),a
  ld hl,0x0100
  ret
rt_input_b: ld hl,(rt_rx_head)
  ld a,h
  cp l
  jr z,rt_input_none
  ld l,h
  ld h,{page}
  ld e,(hl)
  inc a
  ld (rt_rx_tail),a
  ld a,(rt_rx_held)
  or a
  jr z,rt_input_ok
  ld hl,(rt_rx_head)
  ld a,l
  sub h
  cp 129
  jr nc,rt_input_ok
  di
  xor a
  ld (rt_rx_held),a
  ld a,0x96
  out (0x80),a
  ei
rt_input_ok: ld a,1
  ld (rt_consumed),a
  ld l,e
  ld h,0
  ret
rt_input_none: ld hl,0xFFFF
  ret
", []⟩,
  ⟨"
rt_out_byte: ld c,a
rt_out_byte_w: in a,(0x80)
  and 2
  jr z,rt_out_byte_w
  ld a,c
  out (0x81),a
  ld hl,(rt_frame_tx)
  inc hl
  ld (rt_frame_tx),hl
  ret
", []⟩,
  (if trace ≥ 1 then ⟨"
rt_out_end: ld hl,rt_s_tx
  call rt_dbg_str
  ld hl,(rt_frame_tx)
  call rt_dbg_dec
  ld hl,0
  ld (rt_frame_tx),hl
  jp rt_nl
", cstr "rt_s_tx" "tx "⟩ else ⟨"
rt_out_end: ld hl,0
  ld (rt_frame_tx),hl
  ret
", []⟩),
  ⟨"
rt_dbg_str: ld a,(hl)
  or a
  ret z
  out (0xC0),a
  inc hl
  jr rt_dbg_str
", []⟩,
  ⟨"
rt_nl: ld a,10
  out (0xC0),a
  ret
", []⟩,
  ⟨"
rt_dbg_dec: ld b,0
  ld de,10000
  call rt_dbg_dig
  ld de,1000
  call rt_dbg_dig
  ld de,100
  call rt_dbg_dig
  ld de,10
  call rt_dbg_dig
  ld a,l
  add a,48
  out (0xC0),a
  ret
rt_dbg_dig: ld a,47
rt_dbg_dig_l: inc a
  or a
  sbc hl,de
  jr nc,rt_dbg_dig_l
  add hl,de
  cp 48
  jr nz,rt_dbg_dig_p
  inc b
  dec b
  ret z
rt_dbg_dig_p: ld b,1
  out (0xC0),a
  ret
", []⟩,
  (if trace ≥ 2 then ⟨s!"
rt_drop: push af
  ld hl,rt_s_drop
  call rt_dbg_str
  pop af
  cp {drops.length}
  jr nc,rt_drop_c
  ld l,a
  ld h,0
  add hl,hl
  ld de,rt_drop_names
  add hl,de
  ld a,(hl)
  inc hl
  ld h,(hl)
  ld l,a
  call rt_dbg_str
  jp rt_nl
rt_drop_c: push af
  ld hl,rt_s_code
  call rt_dbg_str
  pop af
  ld l,a
  ld h,0
  call rt_dbg_dec
  jp rt_nl
", cstr "rt_s_drop" "drop reason=" ++ cstr "rt_s_code" "code-" ++ nameTable "rt_drop_names" drops⟩
   else ⟨"
rt_drop: ret
", []⟩),
  (if trace ≥ 2 then ⟨s!"
rt_note: push af
  ld hl,rt_s_note
  call rt_dbg_str
  pop af
  cp {notes.length}
  jr nc,rt_note_c
  ld l,a
  ld h,0
  add hl,hl
  ld de,rt_note_names
  add hl,de
  ld a,(hl)
  inc hl
  ld h,(hl)
  ld l,a
  call rt_dbg_str
  jr rt_note_v
rt_note_c: push af
  ld hl,rt_s_noten
  call rt_dbg_str
  pop af
  ld l,a
  ld h,0
  call rt_dbg_dec
rt_note_v: ld a,32
  out (0xC0),a
  ld hl,(rt_acc)
  call rt_dbg_dec
  jp rt_nl
", cstr "rt_s_note" "note " ++ cstr "rt_s_noten" "note-" ++ nameTable "rt_note_names" notes⟩
   else ⟨"
rt_note: ret
", []⟩),
  ⟨"
rt_trap: ld hl,rt_s_trap
  call rt_dbg_str
rt_trap_l: di
  halt
  jr rt_trap_l
", cstr "rt_s_trap" "note trap\n"⟩]

/-- RAM the routines use: name and bytes. -/
def cells : List (String × Nat) :=
  [("rt_acc", 8), ("rt_t1", 8), ("rt_t2", 8), ("rt_n", 1), ("rt_ma", 4), ("rt_mt", 64), ("rt_mn", 1),
   ("rt_consumed", 1), ("rt_before", 1), ("rt_idle", 1)]

def symsOf (items : List Item) : List String :=
  items.flatMap fun it =>
    let vals : List Val := match it with
      | .ins i => i.args.filterMap fun x => match x with
        | .imm v | .mem v => some v
        | _ => none
      | .db vs | .dw vs => vs
      | _ => []
    vals.filterMap fun v => match v with | .sym s _ => some s | _ => none

def labelsOf (items : List Item) : List String :=
  items.filterMap fun it => match it with | .label n => some n | _ => none

/-- The pieces the items refer to, transitively, and the RAM cells used. -/
def select (from_ : List Piece) (items : List Item) : Except String (List Item × List (String × Nat)) := do
  let parsed ← from_.mapM fun p => do return (← Asm.parse p.src) ++ p.items
  let mut have_ : List String := labelsOf items
  let mut out : List Item := []
  let mut pending := symsOf items
  let mut used : List String := pending
  let mut taken : List Nat := []
  while !pending.isEmpty do
    let s := pending.head!
    pending := pending.tail!
    if have_.contains s then continue
    match (List.range parsed.length).find? fun k => (labelsOf parsed[k]!).contains s with
    | none => pure ()      -- a RAM cell, a global, a frame: defined by the caller
    | some k =>
      if taken.contains k then continue
      taken := k :: taken
      let piece := parsed[k]!
      out := out ++ piece
      have_ := have_ ++ labelsOf piece
      let more := symsOf piece
      used := used ++ more
      pending := pending ++ more
  return (out, cells.filter fun (n, _) => used.contains n)

end Ember.Z80.Runtime
