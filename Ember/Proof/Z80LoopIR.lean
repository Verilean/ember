import Ember.Proof.Z80PlanOf
import Ember.Net.Loop

/-!
# Ember.Proof.Z80LoopIR — the loopback program's IR, written out (plan M7.3)

`Loop.ir` is what `IR.lower` returns for `Ember.Net.Loop.prog` (the SLIP
half of the stack and nothing else), as a term: the kernel can run the
code generator and the checks of `Z80Check` on it, which it cannot on
`IR.lower` itself.  That it is the lowering is a `#guard` — evaluated
when this file is built, not proved.

Generated: `repr` of the functions of the lowered program.
-/

namespace Ember.Proof.Z80Gen.Loop
open Ember.Z80

def slip_send : IR.Fn :=
  { name := "slip_send", regParam := some (2, { area := IR.Area.frame "slip_send", off := 0 }), frame := 7, body := #[
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.const 192)] none,
      IR.Instr.mov 2 (IR.Dst.slot { area := IR.Area.frame "slip_send", off := 2 }) (IR.Opd.const 0),
      IR.Instr.mov 2 (IR.Dst.slot { area := IR.Area.frame "slip_send", off := 4 }) (IR.Opd.slot { area := IR.Area.frame "slip_send", off := 0 }),
      IR.Instr.label 0,
      IR.Instr.br (IR.Cmp.ge) 2 (IR.Opd.slot { area := IR.Area.frame "slip_send", off := 2 }) (IR.Opd.slot { area := IR.Area.frame "slip_send", off := 4 }) 1,
      IR.Instr.load 1 (IR.Dst.slot { area := IR.Area.frame "slip_send", off := 6 }) { root := IR.Root.static { area := IR.Area.global "buf", off := 0 }, off := 0, idx := some { opd := IR.Opd.slot { area := IR.Area.frame "slip_send", off := 2 }, size := 2, scale := 1, len := some 296, bound := some 296 } },
      IR.Instr.br (IR.Cmp.ne) 1 (IR.Opd.slot { area := IR.Area.frame "slip_send", off := 6 }) (IR.Opd.const 192) 2,
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.const 219)] none,
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.const 220)] none,
      IR.Instr.jmp 3,
      IR.Instr.label 2,
      IR.Instr.br (IR.Cmp.ne) 1 (IR.Opd.slot { area := IR.Area.frame "slip_send", off := 6 }) (IR.Opd.const 219) 4,
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.const 219)] none,
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.const 221)] none,
      IR.Instr.jmp 5,
      IR.Instr.label 4,
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.slot { area := IR.Area.frame "slip_send", off := 6 })] none,
      IR.Instr.label 5,
      IR.Instr.label 3,
      IR.Instr.bin (IR.Bin.add) 2 (IR.Dst.slot { area := IR.Area.frame "slip_send", off := 2 }) (IR.Opd.slot { area := IR.Area.frame "slip_send", off := 2 }) (IR.Opd.const 1),
      IR.Instr.jmp 0,
      IR.Instr.label 1,
      IR.Instr.eff (Ember.Lang.Effect.outByte) [(1, IR.Opd.const 192)] none,
      IR.Instr.eff (Ember.Lang.Effect.outEnd) [] none,
      IR.Instr.ret none], tmps := #[], inlined := [], dead := false }

def slip_store : IR.Fn :=
  { name := "slip_store", regParam := some (1, { area := IR.Area.frame "slip_store", off := 0 }), frame := 1, body := #[
      IR.Instr.br (IR.Cmp.eq) 1 (IR.Opd.slot { area := IR.Area.global "over", off := 0 }) (IR.Opd.const 0) 0,
      IR.Instr.mov 1 (IR.Dst.slot { area := IR.Area.global "esc", off := 0 }) (IR.Opd.const 0),
      IR.Instr.ret none,
      IR.Instr.label 0,
      IR.Instr.br (IR.Cmp.ge) 2 (IR.Opd.slot { area := IR.Area.global "len", off := 0 }) (IR.Opd.const 296) 1,
      IR.Instr.store 1 { root := IR.Root.static { area := IR.Area.global "buf", off := 0 }, off := 0, idx := some { opd := IR.Opd.slot { area := IR.Area.global "len", off := 0 }, size := 2, scale := 1, len := none, bound := some 296 } } (IR.Opd.slot { area := IR.Area.frame "slip_store", off := 0 }),
      IR.Instr.bin (IR.Bin.add) 2 (IR.Dst.slot { area := IR.Area.global "len", off := 0 }) (IR.Opd.slot { area := IR.Area.global "len", off := 0 }) (IR.Opd.const 1),
      IR.Instr.jmp 2,
      IR.Instr.label 1,
      IR.Instr.mov 1 (IR.Dst.slot { area := IR.Area.global "over", off := 0 }) (IR.Opd.const 1),
      IR.Instr.mov 2 (IR.Dst.slot { area := IR.Area.global "len", off := 0 }) (IR.Opd.const 0),
      IR.Instr.label 2,
      IR.Instr.mov 1 (IR.Dst.slot { area := IR.Area.global "esc", off := 0 }) (IR.Opd.const 0),
      IR.Instr.ret none], tmps := #[], inlined := [], dead := false }

def loop_rx : IR.Fn :=
  { name := "loop_rx", regParam := some (1, { area := IR.Area.frame "loop_rx", off := 0 }), frame := 1, body := #[
      IR.Instr.br (IR.Cmp.ne) 1 (IR.Opd.slot { area := IR.Area.frame "loop_rx", off := 0 }) (IR.Opd.const 192) 0,
      IR.Instr.br (IR.Cmp.eq) 1 (IR.Opd.slot { area := IR.Area.global "over", off := 0 }) (IR.Opd.const 0) 1,
      IR.Instr.eff (Ember.Lang.Effect.drop) [(1, IR.Opd.const 0)] none,
      IR.Instr.jmp 2,
      IR.Instr.label 1,
      IR.Instr.br (IR.Cmp.eq) 2 (IR.Opd.slot { area := IR.Area.global "len", off := 0 }) (IR.Opd.const 0) 3,
      IR.Instr.call "slip_send" none (some (2, IR.Opd.slot { area := IR.Area.global "len", off := 0 })),
      IR.Instr.label 3,
      IR.Instr.label 2,
      IR.Instr.mov 2 (IR.Dst.slot { area := IR.Area.global "len", off := 0 }) (IR.Opd.const 0),
      IR.Instr.mov 1 (IR.Dst.slot { area := IR.Area.global "esc", off := 0 }) (IR.Opd.const 0),
      IR.Instr.mov 1 (IR.Dst.slot { area := IR.Area.global "over", off := 0 }) (IR.Opd.const 0),
      IR.Instr.ret none,
      IR.Instr.label 0,
      IR.Instr.br (IR.Cmp.eq) 1 (IR.Opd.slot { area := IR.Area.global "esc", off := 0 }) (IR.Opd.const 0) 4,
      IR.Instr.br (IR.Cmp.ne) 1 (IR.Opd.slot { area := IR.Area.frame "loop_rx", off := 0 }) (IR.Opd.const 220) 5,
      IR.Instr.call "slip_store" none (some (1, IR.Opd.const 192)),
      IR.Instr.jmp 6,
      IR.Instr.label 5,
      IR.Instr.br (IR.Cmp.ne) 1 (IR.Opd.slot { area := IR.Area.frame "loop_rx", off := 0 }) (IR.Opd.const 221) 7,
      IR.Instr.call "slip_store" none (some (1, IR.Opd.const 219)),
      IR.Instr.jmp 8,
      IR.Instr.label 7,
      IR.Instr.call "slip_store" none (some (1, IR.Opd.slot { area := IR.Area.frame "loop_rx", off := 0 })),
      IR.Instr.label 8,
      IR.Instr.label 6,
      IR.Instr.ret none,
      IR.Instr.label 4,
      IR.Instr.br (IR.Cmp.ne) 1 (IR.Opd.slot { area := IR.Area.frame "loop_rx", off := 0 }) (IR.Opd.const 219) 9,
      IR.Instr.mov 1 (IR.Dst.slot { area := IR.Area.global "esc", off := 0 }) (IR.Opd.const 1),
      IR.Instr.jmp 10,
      IR.Instr.label 9,
      IR.Instr.call "slip_store" none (some (1, IR.Opd.slot { area := IR.Area.frame "loop_rx", off := 0 })),
      IR.Instr.label 10,
      IR.Instr.ret none], tmps := #[], inlined := [], dead := false }

def main : IR.Fn :=
  { name := "main", regParam := none, frame := 2, body := #[
      IR.Instr.eff (Ember.Lang.Effect.inputNext) [] (some (2, IR.Dst.slot { area := IR.Area.frame "main", off := 0 })),
      IR.Instr.br (IR.Cmp.ge) 2 (IR.Opd.slot { area := IR.Area.frame "main", off := 0 }) (IR.Opd.const 256) 0,
      IR.Instr.call "loop_rx" none (some (1, IR.Opd.slot { area := IR.Area.frame "main", off := 0 })),
      IR.Instr.label 0,
      IR.Instr.ret none], tmps := #[], inlined := [], dead := false }

def ir : IR.Prog :=
  { globals :=
      [{ name := "MTU", size := 2, init := some (ByteArray.mk #[40, 1]), const := true },
       { name := "D_OVERSIZE", size := 1, const := true },
       { name := "buf", size := 296 },
       { name := "len", size := 2 },
       { name := "esc", size := 1 },
       { name := "over", size := 1 }],
    fns := [slip_send, slip_store, loop_rx, main],
    entry := "main" }

def sameFn (a b : IR.Fn) : Bool :=
  a.name == b.name && a.regParam == b.regParam && a.frame == b.frame && a.body == b.body && a.tmps == b.tmps &&
    a.inlined == b.inlined && a.dead == b.dead

def sameGlobal (a b : IR.Global) : Bool :=
  a.name == b.name && a.size == b.size && a.const == b.const && a.init.map (·.toList) == b.init.map (·.toList)

def sameProg (p q : IR.Prog) : Bool :=
  p.entry == q.entry && p.fns.length == q.fns.length && (p.fns.zip q.fns).all (fun x => sameFn x.1 x.2) &&
    p.globals.length == q.globals.length && (p.globals.zip q.globals).all (fun x => sameGlobal x.1 x.2)

/-- The lowering of the loopback program is `ir`. -/
def irIsLowering : Bool :=
  match Ember.Net.Loop.prog.check with
  | .ok q =>
    match IR.lower q with
    | .ok r => sameProg r ir
    | .error _ => false
  | .error _ => false

#guard irIsLowering

end Ember.Proof.Z80Gen.Loop
