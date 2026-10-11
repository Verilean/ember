import Ember.Z80.IRInterp

/-!
# Ember.Z80.IRSem — the IR's semantics as total functions (plan M7)

`Ember.Z80.IRInterp` is the interpreter: a `partial` loop in a state
monad, which the kernel cannot unfold.  This file gives the same
semantics in the form proofs need, as `Ember.Lang.Sem` does for Ember
and `Ember.C.Sem` for the emitted C: recursion on fuel (one unit per
instruction and per call), a result that is finished, trapped, out of
fuel, or malformed (an unknown function or label).

Memory is the same 64 KB of bytes at the addresses a `Layout` gives;
`rd` and `wr` are little-endian and wrap at the top, as the
interpreter's.  Nothing here is proved equal to the interpreter: the two
are run against each other (`Tests/Ember/Z80Tests.lean`, "IR semantics").
-/

namespace Ember.Z80.IR.Sem
open Ember.Lang Ember.Trace

structure St where
  mem : ByteArray
  world : World
  deriving Inhabited

/-- `n` bytes at `a`, little-endian. -/
def rd (m : ByteArray) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (m.get! (a % 65536)).toNat + 256 * rd m (a + 1) n

def wr (m : ByteArray) (a : Nat) : Nat → Nat → ByteArray
  | 0, _ => m
  | n + 1, v => wr (m.set! (a % 65536) (UInt8.ofNat (v % 256))) (a + 1) n (v / 256)

/-- How a function ends. -/
inductive Res where
  | ok (r : Option Nat) (st : St)
  | trap (st : St)
  | fuel
  /-- Not a well-formed program: an unknown function or label. -/
  | bad
  deriving Inhabited

def opd (c : Ctx) (st : St) (tmps : Array Nat) (n : Nat) : Opd → Nat
  | .const v => modN n v
  | .slot sl => rd st.mem (c.layout.addr sl) n
  | .tmp t => modN n (tmps.getD t 0)

/-- The address; `none`: the index is out of range (a trap). -/
def addr (c : Ctx) (st : St) (tmps : Array Nat) (a : Addr) : Option Nat :=
  let base := match a.root with
    | .static sl => c.layout.addr sl
    | .ptr p => rd st.mem (c.layout.addr p) 2
  match a.idx with
  | none => some (base + a.off)
  | some x =>
    let i := opd c st tmps x.size x.opd
    match x.len with
    | some len => if i < len then some (base + a.off + i * x.scale) else none
    | none => some (base + a.off + i * x.scale)

def setDst (c : Ctx) (st : St) (tmps : Array Nat) (n : Nat) (d : Dst) (v : Nat) : St × Array Nat :=
  match d with
  | .slot sl => ({ st with mem := wr st.mem (c.layout.addr sl) n v }, tmps)
  | .tmp t => (st, tmps.setIfInBounds t (modN n v))

def isLabel (l : Nat) : Instr → Bool
  | .label l' => l' == l
  | _ => false

def labelAt (f : Fn) (l : Nat) : Option Nat := f.body.findIdx? (isLabel l)

/-- The effects, on the world. -/
def effect (c : Ctx) (w : World) (e : Effect) (vs : List Nat) : Option Nat × World :=
  match e with
  | .inputNext | .ringPop => let r := w.next; (some r.1.toNat, r.2)
  | .inputFrame => let r := w.nextFramed; (some r.1.toNat, r.2)
  | .outByte => (none, { w with frame := w.frame.push (UInt8.ofNat (vs.getD 0 0 % 256)) })
  | .outEnd => (none, { (w.emit (.tx w.frame)) with frame := .empty })
  | .drop =>
    let k := vs.getD 0 0
    (none, w.emit (.drop (c.dropReasons.getD k s!"code-{k}")))
  | .note =>
    let k := vs.getD 0 0
    (none, w.emit (.note s!"{c.notes.getD k s!"note-{k}"} {vs.getD 1 0}"))
  | .mmioRead32 => (some ((w.mmio.get? (UInt32.ofNat (vs.getD 0 0))).getD 0).toNat, w)
  | .mmioWrite32 =>
    (none, { w with mmio := w.mmio.insert (UInt32.ofNat (vs.getD 0 0)) (UInt32.ofNat (vs.getD 1 0)) })

/-- What one instruction does. -/
inductive Step where
  /-- On to the next instruction. -/
  | next (st : St) (tmps : Array Nat)
  | goto (l : Nat)
  /-- Call `g` from the state `st`, the result to `ret`. -/
  | call (g : String) (st : St) (ret : Option (Nat × Dst))
  /-- The function ends. -/
  | stop (r : Res)
  deriving Inhabited

def Step.set (r : St × Array Nat) : Step := .next r.1 r.2

/-- The state after a call or an effect: its result stored. -/
def setRet (c : Ctx) (st : St) (tmps : Array Nat) (ret : Option (Nat × Dst)) (r : Option Nat) : St × Array Nat :=
  match ret with
  | some (n, d) => setDst c st tmps n d (r.getD 0)
  | none => (st, tmps)

def step (c : Ctx) (st : St) (tmps : Array Nat) : Instr → Step
  | .mov n d src => .set (setDst c st tmps n d (opd c st tmps n src))
  | .bin op n d a b => .set (setDst c st tmps n d (binOp op n (opd c st tmps n a) (opd c st tmps n b)))
  | .shift left n d a m amt =>
    .set (setDst c st tmps n d
      (if opd c st tmps m amt ≥ 8 * n then 0
       else if left then modN n (opd c st tmps n a <<< opd c st tmps m amt)
       else opd c st tmps n a >>> opd c st tmps m amt))
  | .not n d a => .set (setDst c st tmps n d (2 ^ (8 * n) - 1 - opd c st tmps n a))
  | .neg n d a => .set (setDst c st tmps n d (modN n (2 ^ (8 * n) - opd c st tmps n a)))
  | .ext n d m src => .set (setDst c st tmps n d (modN n (opd c st tmps m src)))
  | .cmp op n d a b =>
    .set (setDst c st tmps 1 d (if cmpOp op (opd c st tmps n a) (opd c st tmps n b) then 1 else 0))
  | .br op n a b l => if cmpOp op (opd c st tmps n a) (opd c st tmps n b) then .goto l else .next st tmps
  | .jmp l => .goto l
  | .label _ => .next st tmps
  | .load n d p =>
    match addr c st tmps p with
    | some a => .set (setDst c st tmps n d (rd st.mem a n))
    | none => .stop (.trap st)
  | .store n p src =>
    match addr c st tmps p with
    | some a => .next { st with mem := wr st.mem a n (opd c st tmps n src) } tmps
    | none => .stop (.trap st)
  | .lea d p =>
    match addr c st tmps p with
    | some a => .set (setDst c st tmps 2 d (a % 65536))
    | none => .stop (.trap st)
  | .zero sl n => .next { st with mem := wr st.mem (c.layout.addr sl) n 0 } tmps
  | .call g ret reg =>
    .call g
      (match reg, c.prog.fn? g with
       | some (n, o), some gf =>
         match gf.regParam with
         | some (_, sl) => { st with mem := wr st.mem (c.layout.addr sl) n (opd c st tmps n o) }
         | none => st
       | _, _ => st) ret
  | .eff e args ret =>
    .set (setRet c { st with world := (effect c st.world e (args.map fun a => opd c st tmps a.1 a.2)).2 } tmps ret
      (effect c st.world e (args.map fun a => opd c st tmps a.1 a.2)).1)
  | .ret v => .stop (.ok (v.map fun a => opd c st tmps a.1 a.2) st)
  | .trap => .stop (.trap st)

mutual

/-- Run `f` from instruction `pc`. -/
def exec : Nat → Ctx → Fn → Nat → Array Nat → St → Res
  | 0, _, _, _, _, _ => .fuel
  | k + 1, c, f, pc, tmps, st =>
    match f.body[pc]? with
    | none => .ok none st
    | some ins =>
      match step c st tmps ins with
      | .next st' tmps' => exec k c f (pc + 1) tmps' st'
      | .goto l =>
        match labelAt f l with
        | some i => exec k c f i tmps st
        | none => .bad
      | .call g st1 ret =>
        match callF k c g st1 with
        | .ok r st2 => exec k c f (pc + 1) (setRet c st2 tmps ret r).2 (setRet c st2 tmps ret r).1
        | .trap st2 => .trap st2
        | .fuel => .fuel
        | .bad => .bad
      | .stop r => r

def callF : Nat → Ctx → String → St → Res
  | 0, _, _, _ => .fuel
  | k + 1, c, g, st =>
    match c.prog.fn? g with
    | some f => exec k c f 0 (Array.replicate f.tmps.size 0) st
    | none => .bad

end

/-- The driver of `Ember.Z80.IR.run`, on this semantics. -/
def run (lp : Lang.Prog) (inputs : Array Input) (header : Header := { impl := "irsem" })
    (fuel : Nat := 10000000) (inline := false) : Except String Trace := do
  let lp ← match lp.check with
    | .ok p => pure p
    | .error e => throw e.toString
  let p ← lower lp inline
  let (l, st0) := initial p inputs lp.framed
  validate p l (fun f => ((p.fn? f).map (·.frame)).getD 0) 0x8000 0x10000
  let c : Ctx := { prog := p, layout := l, dropReasons := lp.dropReasons, notes := lp.notes }
  let mut st : St := { mem := st0.mem, world := st0.world }
  let mut idle := 0
  let mut trapped : Option String := none
  while !st.world.normalize.done && idle < 3 do
    let before := (st.world.pos, st.world.off)
    match callF fuel c p.entry st with
    | .ok _ st' =>
      st := st'
      idle := if (st.world.pos, st.world.off) == before then idle + 1 else 0
    | .trap st' => st := st'; trapped := some "trap"; break
    | .fuel => trapped := some "out of fuel"; break
    | .bad => throw "malformed IR"
  let w := st.world
  let mut lines : Array Line := #[]
  for i in [0:w.inputs.size] do
    lines := lines.push ⟨i, match w.inputs[i]! with | .rx b => .rx b | .tick => .tick⟩
    for (k, e) in w.events do
      if k == i then lines := lines.push ⟨i, e⟩
  if let some e := trapped then lines := lines.push ⟨w.cur, .note s!"trap {e}"⟩
  return { header, lines }

end Ember.Z80.IR.Sem
