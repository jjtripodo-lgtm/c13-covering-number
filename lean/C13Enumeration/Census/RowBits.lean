import C13Raw.Coding

namespace C13.Enumeration.Census
open C13.Checker.RawSupport
set_option Elab.async false

def rowBits {n : Nat} : List (Fin n) → BitVec n
  | [] => 0
  | i :: rest => ((1 : BitVec n) <<< i.val) ||| rowBits rest

theorem singleton_bit {n : Nat} (i j : Fin n) :
    (((1 : BitVec n) <<< i.val).getLsbD j.val = true) ↔ j = i := by
  rw [BitVec.getLsbD_shiftLeft]
  have h1 : (1 : BitVec n).getLsbD (j.val-i.val) =
      (decide (0 < n) && decide (j.val-i.val = 0)) := BitVec.getLsbD_one
  rw [h1]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  constructor
  · intro h
    apply Fin.ext
    omega
  · intro h
    subst j
    have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
    simp [i.isLt,hn]

theorem rowBits_bit {n : Nat} (row : List (Fin n)) (i : Fin n) :
    (rowBits row).getLsbD i.val = true ↔ i ∈ row := by
  induction row with
  | nil => simp [rowBits]
  | cons j rest ih =>
    simp only [rowBits, BitVec.getLsbD_or, Bool.or_eq_true, singleton_bit,
      ih, List.mem_cons]

def fits {n : Nat} (bits allowed : BitVec n) : Bool :=
  bits &&& allowed == bits

theorem fits_iff {n : Nat} (row : List (Fin n)) (allowed : BitVec n) :
    fits (rowBits row) allowed = true ↔ ∀ i ∈ row, allowed.getLsbD i.val = true := by
  unfold fits
  rw [beq_iff_eq]
  constructor
  · intro h i hi
    have hb := (rowBits_bit row i).2 hi
    have hx := congrArg (fun x : BitVec n => x.getLsbD i.val) h
    simpa [hb] using hx
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases hb : (rowBits row).getLsbD i = true
    · have ha := h ⟨i,hi⟩ ((rowBits_bit row ⟨i,hi⟩).1 hb)
      simp [hb,ha]
    · have hf : (rowBits row).getLsbD i = false := Bool.eq_false_iff.mpr hb
      simp [hf]

theorem no_row_fits {n : Nat} (rows : List (List (Fin n)))
    (bits : List (BitVec n)) (hbits : rows.map rowBits = bits)
    (allowed : BitVec n) (empty : bits.all (fun b => !(fits b allowed)) = true) :
    ∀ row ∈ rows, ¬ (∀ i ∈ row, allowed.getLsbD i.val = true) := by
  intro row hr h
  have hb : rowBits row ∈ bits := hbits ▸ List.mem_map.mpr ⟨row,hr,rfl⟩
  have hh := (List.all_eq_true.mp empty) (rowBits row) hb
  have hf := (fits_iff row allowed).2 h
  simp [hf] at hh

end C13.Enumeration.Census
