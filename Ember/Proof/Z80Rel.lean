import Ember.Proof.Z80Run
import Ember.Proof.Z80Wp
import Ember.Proof.IRMem

/-!
# Ember.Proof.Z80Rel — generated code against the IR: the relation (plan M7.3)

The setting of the proofs about `Ember.Z80.Codegen`:

* `ZCtx`: an assembled image, the IR program with the layout the image
  was built for, and the bytes of memory the two share (`data`);
* `Rel`: a CPU state and an IR state agree — the image is in ROM, the
  shared bytes are equal, a temporary with a slot has its value there
  once it is assigned, and the registers hold what the generator's
  tracker (`Codegen.Regs`) says they hold;
* `GFinal`, `GExt`: the items a function's generation ends with are in
  the image, and those emitted so far are a prefix of them — so the item
  an `ins` appends is at a known index of the image.
-/

namespace Ember.Proof.Z80Gen
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Codegen Ember.Z80.Asm
open Ember.Proof.Z80Enc
open Ember.Z80.IR (Opd Dst Slot Area)

structure ZCtx where
  items : List Item
  a : Assembled
  addrs : List Nat
  c : IR.Ctx
  inp : UInt16 → UInt8
  /-- The bytes the generated code and the IR share. -/
  data : Nat → Prop

/-- The name `n` is the number `v` in the image. -/
def ZCtx.sym (Z : ZCtx) (n : String) (v : Nat) : Prop := Z.a.labels.reverse.lookup n = some v

structure ZCtx.OK (Z : ZCtx) : Prop where
  placed : Placed Z.items 0 Z.a Z.addrs
  /-- The image was built for the layout. -/
  areas : ∀ ar ad, Z.c.layout.areaAddr ar = some ad → Z.sym (areaSym ar) ad

/-- The slot of the temporary `t`. -/
def tmpAddr (Z : ZCtx) (E : GEnv) (t : Nat) : Nat :=
  Z.c.layout.addr { area := .frame E.fn.name, off := E.tmpOff[t]! }

/-- **The relation.**  `dt`: the temporaries assigned so far. -/
structure Rel (Z : ZCtx) (E : GEnv) (dt : Nat → Prop) (regs : Regs) (ist : IR.Sem.St) (tmps : Array Nat)
    (s : Cpu) : Prop where
  img : Img Z.a 0 s
  run : s.halted = false
  mem : ∀ x, Z.data x → s.mem.get! x = ist.mem.get! x
  tmp : ∀ t, dt t → E.spilled[t]! = true →
    IR.Sem.rd s.mem (tmpAddr Z E t) (E.fn.tmps[t]!) = tmps.getD t 0
  ra : ∀ o, o ∈ regs.a → s.a.toNat = IR.Sem.opd Z.c ist tmps 1 o
  rhl : ∀ o, o ∈ regs.hl → s.hl.toNat = IR.Sem.opd Z.c ist tmps 2 o

/-- A step that changes registers only. -/
theorem Rel.regs_only {Z : ZCtx} {E : GEnv} {dt : Nat → Prop} {regs regs' : Regs} {ist : IR.Sem.St}
    {tmps : Array Nat} {s s' : Cpu} (R : Rel Z E dt regs ist tmps s) (hm : s'.mem = s.mem)
    (hr : s'.ramStart = s.ramStart) (hh : s'.halted = s.halted)
    (ha : ∀ o, o ∈ regs'.a → s'.a.toNat = IR.Sem.opd Z.c ist tmps 1 o)
    (hhl : ∀ o, o ∈ regs'.hl → s'.hl.toNat = IR.Sem.opd Z.c ist tmps 2 o) : Rel Z E dt regs' ist tmps s' :=
  ⟨R.img.congr hr hm, by rw [hh]; exact R.run, fun x hx => by rw [hm]; exact R.mem x hx,
    fun t h1 h2 => by rw [hm]; exact R.tmp t h1 h2, ha, hhl⟩

/-! ## The code being generated is in the image -/

/-- The items generation ends with are in the image from the item `base` on. -/
structure GFinal (Z : ZCtx) (base : Nat) (sF : GS) : Prop where
  code : ∀ j it, sF.out[j]? = some it → Z.items[base + j]? = some it

/-- `s'` is `s` with more items emitted. -/
def GExt (s s' : GS) : Prop := s.out.toList <+: s'.out.toList

theorem GExt.refl (s : GS) : GExt s s := List.prefix_refl _

theorem GExt.trans {s s' s'' : GS} (h1 : GExt s s') (h2 : GExt s' s'') : GExt s s'' := List.IsPrefix.trans h1 h2

theorem GExt.push (s : GS) (it : Item) : GExt s { s with out := s.out.push it } := by
  simp [GExt]

theorem GExt.regs (s : GS) (r : Regs) : GExt s { s with regs := r } := List.prefix_refl _

theorem GExt.size {s s' : GS} (h : GExt s s') : s.out.size ≤ s'.out.size := by
  simpa using h.length_le

/-- The item just emitted. -/
theorem GFinal.emitted {Z : ZCtx} {base : Nat} {sF : GS} (F : GFinal Z base sF) {s : GS} {out : Array Item}
    {it : Item} (hx : GExt s sF) (ho : s.out = out.push it) : Z.items[base + out.size]? = some it := by
  refine F.code out.size it ?_
  obtain ⟨rest, hr⟩ := hx
  have : sF.out.toList[out.size]? = some it := by
    rw [← hr, ho]
    simp
  simpa using this

/-! ## Numbers -/

theorem mk16_toNat (hi lo : UInt8) : (mk16 hi lo).toNat = hi.toNat * 256 + lo.toNat := by
  have h1 := hi.toNat_lt
  have h2 := lo.toNat_lt
  simp only [mk16, UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16]
  rw [show (8 : UInt16).toNat % 16 = 8 from rfl, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  rw [show hi.toNat * 2 ^ 8 = hi.toNat <<< 8 from (Nat.shiftLeft_eq _ _).symm]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega : lo.toNat < 2 ^ 8), Nat.shiftLeft_eq]

@[simp] theorem lo_mk16 (h l : UInt8) : lo (mk16 h l) = l := by
  apply UInt8.toNat_inj.mp
  have := l.toNat_lt
  simp only [lo, UInt16.toNat_toUInt8, mk16_toNat]
  omega

@[simp] theorem hi_mk16 (h l : UInt8) : hi (mk16 h l) = h := by
  apply UInt8.toNat_inj.mp
  have := l.toNat_lt
  have := h.toNat_lt
  simp only [hi, UInt16.toNat_toUInt8, UInt16.toNat_shiftRight, mk16_toNat]
  rw [show (8 : UInt16).toNat % 16 = 8 from rfl, Nat.shiftRight_eq_div_pow]
  omega

theorem w16_eq (lo hi : UInt8) : w16 lo hi = mk16 hi lo := by
  simp only [w16, mk16, UInt16.or_comm]

theorem hl_toNat (s : Cpu) : s.hl.toNat = s.h.toNat * 256 + s.l.toNat := mk16_toNat _ _

theorem byteOf_toNat (x : Int) : (byteOf x).toNat = (x % 256).toNat := by
  have h0 : 0 ≤ x % 256 := Int.emod_nonneg _ (by decide)
  have h1 : x % 256 < 256 := Int.emod_lt_of_pos _ (by decide)
  simp only [byteOf, UInt8.toNat_ofNat']
  omega

/-- An address the assembler wrote, as the CPU reads it. -/
theorem w16_val (x : Nat) (hx : x < 65536) :
    (w16 (byteOf (Int.ofNat x)) (byteOf (Int.ofNat x / 256))).toNat = x := by
  rw [w16_eq, mk16_toNat, byteOf_toNat, byteOf_toNat]
  have e1 : (Int.ofNat x / 256 % 256).toNat = x / 256 % 256 := by
    show ((x : Int) / 256 % 256).toNat = _
    omega
  have e2 : (Int.ofNat x % 256).toNat = x % 256 := by
    show ((x : Int) % 256).toNat = _
    omega
  rw [e1, e2]
  omega

theorem val_num (env : Env) (n : Int) : env.val (.num n) = n := rfl

theorem val_sym (env : Env) (n : String) (off A : Int) (h : env.resolve n = some A) :
    env.val (.sym n off) = A + off := by
  have hr : (readThe Env : Enc Env) env = Except.ok env := rfl
  simp only [Env.val, value, bind, ReaderT.bind, ReaderT.run, read, Except.bind, hr, h]
  rfl

/-- A slot's address in the image is its address in the layout. -/
theorem slot_val {Z : ZCtx} (ok : Z.OK) (sl : Slot) (ad pc : Nat) (h : Z.c.layout.areaAddr sl.area = some ad) :
    (Z.a.env pc).val (slotVal sl) = Int.ofNat (Z.c.layout.addr sl) := by
  have hs := ok.areas _ _ h
  unfold ZCtx.sym at hs
  rw [slotVal, val_sym _ _ _ (Int.ofNat ad) (by simp [Assembled.env, hs])]
  simp [IR.Layout.addr, h]

/-! ## Memory, as the CPU and as the IR read it -/

theorem rd_one (m : ByteArray) (a : Nat) (ha : a < 65536) : IR.Sem.rd m a 1 = (m.get! a).toNat := by
  simp [IR.Sem.rd, Nat.mod_eq_of_lt ha]

theorem rd_two (m : ByteArray) (a : Nat) (ha : a + 1 < 65536) :
    IR.Sem.rd m a 2 = (m.get! (a + 1)).toNat * 256 + (m.get! a).toNat := by
  simp only [IR.Sem.rd, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : a < 65536)]
  omega

theorem cpu_rd16 (s : Cpu) (x : UInt16) (hx : x.toNat + 1 < 65536) :
    (s.rd16 x).toNat = IR.Sem.rd s.mem x.toNat 2 := by
  rw [rd_two _ _ hx]
  show (w16 (s.rd x) (s.rd (x + 1))).toNat = _
  rw [w16_eq, mk16_toNat]
  have : (x + 1).toNat = x.toNat + 1 := by
    rw [UInt16.toNat_add]
    show (x.toNat + 1) % 65536 = _
    omega
  simp only [Cpu.rd, this]

end Ember.Proof.Z80Gen
