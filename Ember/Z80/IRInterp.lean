import Ember.Z80.Frame

/-!
# Ember.Z80.IRInterp — the IR's semantics, executable (plan M6.3)

Memory is 64 KB of bytes; globals and frames are where a `Layout` puts
them, so a wrong frame overlay shows up as a wrong result here already.
Effects go to the same `World` as the Ember interpreter's, and `run`
drives the entry function the same way: the two interpreters must
produce the same trace (`ember-z80 ir-fuzz`).
-/

namespace Ember.Z80.IR
open Ember.Lang Ember.Trace

structure IState where
  mem : ByteArray := ByteArray.mk (Array.replicate 65536 0)
  world : World
  fuel : Nat := 0
  deriving Inhabited

abbrev IM := ExceptT String (StateM IState)

structure Ctx where
  prog : Prog
  layout : Layout
  dropReasons : List String := []
  notes : List String := []

def rd (a n : Nat) : IM Nat := do
  let m := (← get).mem
  let mut v := 0
  for k in [0:n] do
    v := v + (m.get! ((a + k) % 65536)).toNat <<< (8 * k)
  return v

def wr (a n v : Nat) : IM Unit :=
  modify fun s => Id.run do
    let mut m := s.mem
    let s := { s with mem := ByteArray.empty }
    for k in [0:n] do
      m := m.set! ((a + k) % 65536) (UInt8.ofNat ((v >>> (8 * k)) % 256))
    return { s with mem := m }

def modN (n v : Nat) : Nat := v % 2 ^ (8 * n)

def cmpOp (op : Cmp) (a b : Nat) : Bool :=
  match op with
  | .eq => a == b | .ne => a != b | .lt => a < b | .ge => a ≥ b

def binOp (op : Bin) (n a b : Nat) : Nat :=
  modN n <| match op with
  | .add => a + b
  | .sub => a + 2 ^ (8 * n) - b
  | .mul => a * b
  | .div => if b == 0 then 0 else a / b
  | .mod => if b == 0 then 0 else a % b
  | .and => a &&& b
  | .or => a ||| b
  | .xor => a ^^^ b

def effect (c : Ctx) (e : Effect) (vs : List Nat) : IM (Option Nat) := do
  let s ← get
  let w := s.world
  let set' (w : World) : IM Unit := set { s with world := w }
  match e with
  | .inputNext | .ringPop =>
    let (v, w') := w.next
    set' w'
    return some v.toNat
  | .inputFrame =>
    let (v, w') := w.nextFramed
    set' w'
    return some v.toNat
  | .outByte => set' { w with frame := w.frame.push (UInt8.ofNat (vs[0]! % 256)) }; return none
  | .outEnd => set' { (w.emit (.tx w.frame)) with frame := .empty }; return none
  | .drop =>
    let k := vs[0]!
    set' (w.emit (.drop (c.dropReasons.getD k s!"code-{k}")))
    return none
  | .note =>
    let k := vs[0]!
    set' (w.emit (.note s!"{c.notes.getD k s!"note-{k}"} {vs[1]!}"))
    return none
  | .mmioRead32 => return some ((w.mmio.get? (UInt32.ofNat vs[0]!)).getD 0).toNat
  | .mmioWrite32 =>
    set' { w with mmio := w.mmio.insert (UInt32.ofNat vs[0]!) (UInt32.ofNat vs[1]!) }
    return none

partial def runFn (c : Ctx) (name : String) : IM (Option Nat) := do
  let some f := c.prog.fn? name | throw s!"unknown function {name}"
  let labelAt (l : Nat) : IM Nat :=
    match f.body.findIdx? (· == .label l) with
    | some i => pure i
    | none => throw s!"{name}: no label L{l}"
  let mut tmps : Array Nat := Array.replicate f.tmps.size 0
  let mut pc := 0
  let mut result : Option Nat := none
  while pc < f.body.size do
    let s ← get
    if s.fuel == 0 then throw "out of fuel"
    set { s with fuel := s.fuel - 1 }
    let ins := f.body[pc]!
    pc := pc + 1
    let opd (n : Nat) (o : Opd) : IM Nat :=
      match o with
      | .const v => pure (modN n v)
      | .slot sl => rd (c.layout.addr sl) n
      | .tmp t => pure (modN n tmps[t]!)
    let addr (a : Addr) : IM Nat := do
      let base ← match a.root with
        | .static sl => pure (c.layout.addr sl)
        | .ptr p => rd (c.layout.addr p) 2
      match a.idx with
      | none => return base + a.off
      | some x =>
        let i ← opd x.size x.opd
        if let some len := x.len then
          unless i < len do throw s!"trap: index {i} out of bounds [0, {len}) in {name}"
        return base + a.off + i * x.scale
    -- a destination is written after the instruction's operands are read
    let mut out : Option (Nat × Dst × Nat) := none
    match ins with
    | .mov n d src => out := some (n, d, ← opd n src)
    | .bin op n d a b => out := some (n, d, binOp op n (← opd n a) (← opd n b))
    | .shift left n d a m amt =>
      let x ← opd n a
      let k ← opd m amt
      out := some (n, d, if k ≥ 8 * n then 0 else if left then modN n (x <<< k) else x >>> k)
    | .not n d a => out := some (n, d, 2 ^ (8 * n) - 1 - (← opd n a))
    | .neg n d a => out := some (n, d, modN n (2 ^ (8 * n) - (← opd n a)))
    | .ext n d m src => out := some (n, d, modN n (← opd m src))
    | .cmp op n d a b => out := some (1, d, if cmpOp op (← opd n a) (← opd n b) then 1 else 0)
    | .br op n a b l => if cmpOp op (← opd n a) (← opd n b) then pc ← labelAt l
    | .jmp l => pc ← labelAt l
    | .label _ => pure ()
    | .load n d p => out := some (n, d, ← rd (← addr p) n)
    | .store n p src =>
      let v ← opd n src
      wr (← addr p) n v
    | .lea d p => out := some (2, d, (← addr p) % 65536)
    | .zero sl n => wr (c.layout.addr sl) n 0
    | .call g ret reg =>
      if let (some (n, o), some gf) := (reg, c.prog.fn? g) then
        if let some (_, sl) := gf.regParam then wr (c.layout.addr sl) n (← opd n o)
      let r ← runFn c g
      if let some (n, d) := ret then out := some (n, d, r.getD 0)
    | .eff e args ret =>
      let vs ← args.mapM fun (n, o) => opd n o
      let r ← effect c e vs
      if let some (n, d) := ret then out := some (n, d, r.getD 0)
    | .ret v =>
      if let some (n, o) := v then result := some (← opd n o)
      pc := f.body.size
    | .trap => throw s!"trap in {name}"
    if let some (n, d, v) := out then
      match d with
      | .slot sl => wr (c.layout.addr sl) n v
      | .tmp t => tmps := tmps.set! t (modN n v)
  return result

/-- Lay the program out and set the globals' initial values. -/
def initial (p : Prog) (inputs : Array Input) (framed := false) : Layout × IState := Id.run do
  let l := layout p (fun f => ((p.fn? f).map (·.frame)).getD 0) 0x8000
  let mut mem := ByteArray.mk (Array.replicate 65536 0)
  for g in p.globals do
    if let some bytes := g.init then
      let a := (l.globals.lookup g.name).getD 0
      for k in [0:bytes.size] do mem := mem.set! (a + k) bytes[k]!
  return (l, { mem, world := { inputs, framed } })

/-- The driver of the Ember interpreter (`Lang.runMachine`), on the IR. -/
def run (lp : Lang.Prog) (inputs : Array Input) (header : Header := { impl := "ir" })
    (fuel : Nat := 10000000) (inline := false) : Except String Trace := do
  let lp ← match lp.check with
    | .ok p => pure p
    | .error e => throw e.toString
  let p ← lower lp inline
  let (l, st0) := initial p inputs lp.framed
  validate p l (fun f => ((p.fn? f).map (·.frame)).getD 0) 0x8000 0x10000
  let c : Ctx := { prog := p, layout := l, dropReasons := lp.dropReasons, notes := lp.notes }
  let mut st := st0
  let mut idle := 0
  let mut trapped : Option String := none
  while !st.world.normalize.done && idle < 3 do
    let before := (st.world.pos, st.world.off)
    let (r, st') := (runFn c p.entry).run.run { st with fuel }
    st := st'
    match r with
    | .error e => trapped := some e; break
    | .ok _ => idle := if (st.world.pos, st.world.off) == before then idle + 1 else 0
  let w := st.world
  let mut lines : Array Line := #[]
  for i in [0:w.inputs.size] do
    lines := lines.push ⟨i, match w.inputs[i]! with | .rx b => .rx b | .tick => .tick⟩
    for (k, e) in w.events do
      if k == i then lines := lines.push ⟨i, e⟩
  if let some e := trapped then lines := lines.push ⟨w.cur, .note s!"trap {e}"⟩
  return { header, lines }

end Ember.Z80.IR
