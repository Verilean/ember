import Ember.Proof.Z80Encode
import Ember.Proof.Z80Asm

/-!
# Ember.Proof.Z80Run — running an assembled image, instruction by instruction (plan M7.3)

What the proofs about generated code stand on:

* `Img a s`: the bytes of the assembled image `a` are in the memory of
  the CPU `s`, below `ramStart` — in ROM, where no write changes them
  (`Img.wr`);
* `step_item`: with the program counter at the address of an item that
  is an instruction, one step of the CPU is what `Asm.exec` says the
  instruction does (`assemble_ok` and `step_encode` together);
* `Steps s s'`: the CPU gets from `s` to `s'` in some number of steps.
-/

namespace Ember.Proof.Z80Enc
open Ember.Z80 Ember.Z80.Cpu Ember.Z80.Asm

/-- What `assemble_ok` says of an image: `addrs` are the addresses of its items. -/
def Placed (items : List Item) (origin : Nat) (a : Assembled) (addrs : List Nat) : Prop :=
  addrs[0]? = some origin ∧
    ∀ k it, items[k]? = some it →
      ∃ ad bs, addrs[k]? = some ad ∧ it.encode (a.env ad) = .ok bs ∧ addrs[k + 1]? = some (ad + bs.length) ∧
        origin ≤ ad ∧ (∀ j b, bs[j]? = some b → a.bytes.data[ad - origin + j]? = some b) ∧
        ∀ n, it = Item.label n → a.labels.reverse.lookup n = some ad

theorem placed_of_assemble {items : List Item} {origin : Nat} {a : Assembled} (h : assemble items origin = .ok a) :
    ∃ addrs, Placed items origin a addrs := assemble_ok h

/-- The image is in memory at `origin`, in ROM. -/
structure Img (a : Assembled) (origin : Nat) (s : Cpu) : Prop where
  rom : origin + a.bytes.size ≤ s.ramStart.toNat
  bytes : ∀ x b, a.bytes.data[x]? = some b → s.mem.get! (origin + x) = b

theorem Img.congr {a : Assembled} {origin : Nat} {s s' : Cpu} (I : Img a origin s) (hr : s'.ramStart = s.ramStart)
    (hm : s'.mem = s.mem) : Img a origin s' :=
  ⟨by rw [hr]; exact I.rom, fun x b h => by rw [hm]; exact I.bytes x b h⟩

theorem getBang_set (m : ByteArray) (i : Nat) (b : UInt8) (x : Nat) (h : i ≠ x) : (m.set! i b).get! x = m.get! x := by
  obtain ⟨bs⟩ := m
  simp [ByteArray.set!, ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_ne h]

/-- A write leaves the image. -/
theorem Img.wr {a : Assembled} {origin : Nat} {s : Cpu} (I : Img a origin s) (x : UInt16) (v : UInt8) :
    Img a origin (s.wr x v) := by
  unfold Cpu.wr
  split
  · exact I
  · rename_i hlt
    refine ⟨I.rom, fun y b h => ?_⟩
    have hy : y < a.bytes.size := by
      rcases Nat.lt_or_ge y a.bytes.data.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at h; cases h
    have hge : s.ramStart.toNat ≤ x.toNat := by
      rw [UInt16.not_lt] at hlt
      exact UInt16.le_iff_toNat_le.mp hlt
    have hrom := I.rom
    show (s.mem.set! x.toNat v).get! (origin + y) = b
    rw [getBang_set _ _ _ _ (by omega)]
    exact I.bytes y b h

theorem Img.wr16 {a : Assembled} {origin : Nat} {s : Cpu} (I : Img a origin s) (x v : UInt16) :
    Img a origin (s.wr16 x v) := (I.wr _ _).wr _ _

/-- The bytes of an item are the code at its address. -/
theorem Placed.code {items : List Item} {origin : Nat} {a : Assembled} {addrs : List Nat}
    (P : Placed items origin a addrs) {s : Cpu} (I : Img a origin s) {k : Nat} {it : Item}
    (hk : items[k]? = some it) :
    ∃ ad bs, addrs[k]? = some ad ∧ it.encode (a.env ad) = .ok bs ∧ addrs[k + 1]? = some (ad + bs.length) ∧
      (s.pc.toNat = ad → Code s bs) := by
  obtain ⟨ad, bs, h1, h2, h3, h4, h5, _⟩ := P.2 k it hk
  refine ⟨ad, bs, h1, h2, h3, fun hpc j b hj => ?_⟩
  have hb := h5 j b hj
  have hlt : ad - origin + j < a.bytes.size := by
    rcases Nat.lt_or_ge (ad - origin + j) a.bytes.data.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hb; cases hb
  have hrom := I.rom
  have hr : s.ramStart.toNat < 65536 := s.ramStart.toNat_lt
  have := I.bytes _ b hb
  show s.mem.get! (s.pc + UInt16.ofNat j).toNat = b
  have hto : (s.pc + UInt16.ofNat j).toNat = origin + (ad - origin + j) := by
    rw [UInt16.toNat_add, hpc, UInt16.toNat_ofNat']
    omega
  rw [hto]
  exact this

/-- **One instruction of the image.** -/
theorem step_item {items : List Item} {origin : Nat} {a : Assembled} {addrs : List Nat}
    (P : Placed items origin a addrs) {s s' : Cpu} (I : Img a origin s) {k ad : Nat} {i : Instr}
    (hk : items[k]? = some (.ins i)) (had : addrs[k]? = some ad) (hpc : s.pc.toNat = ad)
    (hh : s.halted = false) {inp : UInt16 → UInt8} (hx : exec (a.env ad) i s inp = some s') :
    s.step inp = s' := by
  obtain ⟨ad', bs, h1, h2, _, hcode⟩ := P.code I hk
  rw [had] at h1
  cases h1
  exact step_encode i h2 (hcode hpc) hh hx

/-! ## Several steps -/

def run (inp : UInt16 → UInt8) : Nat → Cpu → Cpu
  | 0, s => s
  | n + 1, s => run inp n (s.step inp)

/-- The CPU gets from `s` to `s'`. -/
def Steps (inp : UInt16 → UInt8) (s s' : Cpu) : Prop := ∃ n, run inp n s = s'

theorem Steps.refl (inp : UInt16 → UInt8) (s : Cpu) : Steps inp s s := ⟨0, rfl⟩

theorem run_add (inp : UInt16 → UInt8) : ∀ (n m : Nat) (s : Cpu), run inp (n + m) s = run inp m (run inp n s)
  | 0, m, s => by simp [run]
  | n + 1, m, s => by
    rw [show n + 1 + m = (n + m) + 1 by omega, run, run, run_add inp n m]

theorem Steps.trans {inp : UInt16 → UInt8} {s s' s'' : Cpu} (h1 : Steps inp s s') (h2 : Steps inp s' s'') :
    Steps inp s s'' := by
  obtain ⟨n, rfl⟩ := h1
  obtain ⟨m, rfl⟩ := h2
  exact ⟨n + m, run_add inp n m s⟩

theorem Steps.one {inp : UInt16 → UInt8} {s s' : Cpu} (h : s.step inp = s') : Steps inp s s' := ⟨1, h⟩

end Ember.Proof.Z80Enc
