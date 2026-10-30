import C13Covering.Reduction

namespace C13.Enumeration.Census
open Finset
open scoped BigOperators
set_option Elab.async false

/-- Integer certificate soundness. The finite producer supplies coefficients;
the row inequalities and every allowed column bound remain proof obligations. -/
theorem weighted_refutation {I B : Type*} [DecidableEq I] [DecidableEq B]
    (rows : Finset I) (chosen : Finset B) (weight demand : I → Int)
    (incidence : I → B → Int) (bound : Int) (budget : Nat)
    (bound_nonnegative : 0 ≤ bound)
    (row_bounds : ∀ i ∈ rows,
      weight i * demand i ≤ ∑ b ∈ chosen, weight i * incidence i b)
    (column_bounds : ∀ b ∈ chosen,
      (∑ i ∈ rows, weight i * incidence i b) ≤ bound)
    (separation : (budget : Int) * bound < ∑ i ∈ rows, weight i * demand i)
    (size_bound : chosen.card ≤ budget) : False := by
  have h : (∑ i ∈ rows, weight i * demand i) ≤ (budget : Int) * bound := by
    calc
      _ ≤ ∑ i ∈ rows, ∑ b ∈ chosen, weight i * incidence i b :=
        sum_le_sum row_bounds
      _ = ∑ b ∈ chosen, ∑ i ∈ rows, weight i * incidence i b := sum_comm
      _ ≤ ∑ _b ∈ chosen, bound := sum_le_sum column_bounds
      _ = (chosen.card : Int) * bound := by simp
      _ ≤ (budget : Int) * bound :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast size_bound) bound_nonnegative
  exact (not_lt_of_ge h) separation

theorem count_indicator {B : Type*} [DecidableEq B] (chosen : Finset B)
    (p : B → Prop) [DecidablePred p] :
    (∑ b ∈ chosen, (if p b then (1 : Int) else 0)) = ((chosen.filter p).card : Int) := by
  simp [Finset.sum_filter]

theorem positive_cover_row {B : Type*} [DecidableEq B] (chosen : Finset B)
    (p : B → Prop) [DecidablePred p] (weight : Int) (hweight : 0 ≤ weight)
    (covered : ∃ b ∈ chosen, p b) :
    weight ≤ ∑ b ∈ chosen, weight * (if p b then (1 : Int) else 0) := by
  rw [← mul_sum, count_indicator]
  have hcard : 1 ≤ (chosen.filter p).card := by
    apply Finset.card_pos.mpr
    obtain ⟨b,hb,hp⟩ := covered
    exact ⟨b,mem_filter.mpr ⟨hb,hp⟩⟩
  have hc : (1 : Int) ≤ ((chosen.filter p).card : Int) := by exact_mod_cast hcard
  simpa using mul_le_mul_of_nonneg_left hc hweight

theorem exact_degree_row {B : Type*} [DecidableEq B] (chosen : Finset B)
    (p : B → Prop) [DecidablePred p] (weight : Int) (demand : Nat)
    (exact_count : (chosen.filter p).card = demand) :
    weight * (demand : Int) =
      ∑ b ∈ chosen, weight * (if p b then (1 : Int) else 0) := by
  rw [← mul_sum, count_indicator, exact_count]

end C13.Enumeration.Census
