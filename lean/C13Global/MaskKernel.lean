import Mathlib.Data.List.Basic
namespace C13.Global
abbrev Code := BitVec 13
abbrev Mask := Nat

def singletonMask (b : Code) : Mask := 2 ^ b.toNat

def listMask : List Code → Mask
  | [] => 0
  | b :: bs => singletonMask b ||| listMask bs

theorem singletonMask_bit (b c : Code) :
    (singletonMask b).testBit c.toNat = decide (c = b) := by
  simp only [singletonMask, Nat.testBit_two_pow]
  congr 1
  apply propext
  exact ⟨fun h => BitVec.eq_of_toNat_eq h.symm, fun h => by simp [h]⟩

theorem listMask_bit (xs : List Code) (b : Code) :
    (listMask xs).testBit b.toNat = decide (b ∈ xs) := by
  induction xs with
  | nil => simp [listMask]
  | cons c cs ih => simp [listMask,Nat.testBit_or,singletonMask_bit,ih]

abbrev Point := Fin 13

def restrictMask (base : Mask) (alphabets : List Mask) : List Point → Mask
  | [] => base
  | q :: qs => (alphabets.getD q.val 0) &&& restrictMask base alphabets qs

theorem restrictMask_bit (base : Mask) (alphabets : List Mask)
    (points : List Point) (b : Code)
    (hb : base.testBit b.toNat = true)
    (ha : ∀ q ∈ points, (alphabets.getD q.val 0).testBit b.toNat = true) :
    (restrictMask base alphabets points).testBit b.toNat = true := by
  induction points with
  | nil => exact hb
  | cons q qs ih =>
    simp only [restrictMask, Nat.testBit_and]
    rw [ha q (by simp), ih (fun p hp => ha p (by simp [hp]))]
    rfl

theorem masks_disjoint (a c : Mask) (checked : a &&& c = 0) (b : Code)
    (ha : a.testBit b.toNat = true) (hc : c.testBit b.toNat = true) : False := by
  have hh := congrArg (fun m : Nat => m.testBit b.toNat) checked
  simpa [Nat.testBit_and,ha,hc] using hh

theorem mask_subset (a c : Mask) (checked : a &&& c = a) (b : Code)
    (ha : a.testBit b.toNat = true) : c.testBit b.toNat = true := by
  have hh := congrArg (fun m : Nat => m.testBit b.toNat) checked
  simpa [Nat.testBit_and,ha] using hh

theorem mem_of_mask_eq (xs : List Code) (m : Mask) (checked : listMask xs = m)
    (b : Code) (hb : m.testBit b.toNat = true) : b ∈ xs := by
  rw [← checked,listMask_bit] at hb
  exact of_decide_eq_true hb

end C13.Global
