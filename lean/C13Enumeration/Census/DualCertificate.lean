import C13Enumeration.Census.CodeModel
import C13Enumeration.Census.Weighted
import Mathlib.Algebra.BigOperators.Fin

namespace C13.Enumeration.Census
open Finset C13.Checker.RawSupport
open scoped BigOperators
set_option Elab.async false

inductive Test where
  | covers (quad : Code)
  | incident (point : Point)
  | block (code : Code)

def Test.check : Test → Code → Bool
  | .covers t, b => subsetB t b
  | .incident q, b => b.getLsbD q.val
  | .block c, b => b == c

structure LinearRow where
  test : Test
  demand : Int
  weight : Int

def LinearRow.count (r : LinearRow) (chosen : Finset Code) : Int :=
  ((chosen.filter fun b => r.test.check b = true).card : Int)

def LinearRow.Satisfied (r : LinearRow) (chosen : Finset Code) : Prop :=
  r.demand = r.count chosen ∨ (0 ≤ r.weight ∧ r.demand ≤ r.count chosen)

theorem sum_get {A : Type*} (xs : List A) (f : A → Int) :
    (xs.map f).sum = ∑ i : Fin xs.length, f (xs.get i) := by
  rw [← Fin.sum_ofFn]
  change (xs.map f).sum = (List.ofFn (f ∘ (fun i : Fin xs.length => xs.get i))).sum
  rw [← List.map_ofFn]
  simp

def cost (rows : List LinearRow) (b : Code) : Int :=
  (rows.map fun r => r.weight * (if r.test.check b then 1 else 0)).sum

def score (rows : List LinearRow) : Int :=
  (rows.map fun r => r.weight * r.demand).sum

def certificateB (columns : List Code) (rows : List LinearRow)
    (bound : Int) (budget : Nat) : Bool :=
  decide (0 ≤ bound) && decide ((budget : Int) * bound < score rows) &&
    columns.all (fun b => decide (cost rows b ≤ bound))

theorem LinearRow.weighted_bound (r : LinearRow) (chosen : Finset Code)
    (h : r.Satisfied chosen) :
    r.weight * r.demand ≤
      ∑ b ∈ chosen, r.weight * (if r.test.check b then (1 : Int) else 0) := by
  rw [← mul_sum]
  have hc : (∑ b ∈ chosen, (if r.test.check b then (1 : Int) else 0)) = r.count chosen := by
    exact count_indicator chosen (fun b => r.test.check b = true)
  rw [hc]
  rcases h with he | ⟨hw,hd⟩
  · rw [he]
  · exact mul_le_mul_of_nonneg_left hd hw

/-- Every coefficient and every allowed column is checked in Lean. A successful
producer solve or a claimed leaf closure cannot supply this theorem's premise. -/
theorem certificate_sound (columns : List Code) (rows : List LinearRow)
    (bound : Int) (budget : Nat)
    (checked : certificateB columns rows bound budget = true)
    (chosen : Finset Code) (hcolumns : ∀ b ∈ chosen, b ∈ columns)
    (hrows : ∀ i : Fin rows.length, (rows.get i).Satisfied chosen)
    (hcard : chosen.card ≤ budget) : False := by
  have hh : 0 ≤ bound ∧ (budget : Int) * bound < score rows ∧
      columns.all (fun b => decide (cost rows b ≤ bound)) = true := by
    simpa only [certificateB,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using checked
  apply weighted_refutation (Finset.univ : Finset (Fin rows.length)) chosen
    (fun i => (rows.get i).weight) (fun i => (rows.get i).demand)
    (fun i b => if (rows.get i).test.check b then 1 else 0)
    bound budget hh.1
  · intro i _
    exact (rows.get i).weighted_bound chosen (hrows i)
  · intro b hb
    have hbnd := of_decide_eq_true ((List.all_eq_true.mp hh.2.2) b (hcolumns b hb))
    simpa only [cost,sum_get] using hbnd
  · simpa only [score,sum_get] using hh.2.1
  · exact hcard

end C13.Enumeration.Census
