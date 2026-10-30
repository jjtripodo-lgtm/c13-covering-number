import C13Enumeration.Census.RowValidity

namespace C13.Enumeration.Census
open Finset C13.Checker.RawSupport C13.SourceData
set_option Elab.async false
set_option maxRecDepth 10000

instance (K : Family Point) (Q : Finset Point) (fixed : List (Code × Bool))
    (r : LinearRow) : Decidable (ValidRow K Q fixed r) := by
  unfold ValidRow
  split
  · rename_i t ht
    letI : Decidable (∀ B ∈ K, ¬ decodeTyped t ⊆ B) := Finset.decidableDforallFinset
    infer_instance
  · infer_instance
  · infer_instance

inductive CoverTree where
  | leaf (rows : List LinearRow) (bound : Int)
  | split (block : Code) (absent present : CoverTree)

def CoverTree.check (columns : List Code) (K : Family Point) (Q : Finset Point)
    (fixed : List (Code × Bool)) : CoverTree → Bool
  | .leaf rows bound => rows.all (fun r => decide (ValidRow K Q fixed r)) &&
      certificateB columns rows bound 14
  | .split b absent present =>
      absent.check columns K Q ((b,false)::fixed) &&
      present.check columns K Q ((b,true)::fixed)

theorem CoverTree.sound (tree : CoverTree) (columns : List Code)
    (K : Family Point) (Q : Finset Point) (fixed : List (Code × Bool))
    (checked : tree.check columns K Q fixed = true)
    (F : Family Point) (hcover : IsCoverOn univ F 7 4) (hroot : link F hole = K)
    (hQ : Q ⊆ univ.erase hole) (hmin : ∀ q ∈ Q, degree F q = 15)
    (hcolumns : ∀ b ∈ outsideCodes F, b ∈ columns)
    (hfixed : FixedHolds (outsideCodes F) fixed)
    (hcard : (outside F hole).card ≤ 14) : False := by
  induction tree generalizing fixed with
  | leaf rows bound =>
    have hh : rows.all (fun r => decide (ValidRow K Q fixed r)) = true ∧
        certificateB columns rows bound 14 = true := by
      simpa only [CoverTree.check,Bool.and_eq_true] using checked
    apply certificate_sound columns rows bound 14 hh.2 (outsideCodes F) hcolumns
    · intro i
      apply valid_row_satisfied F K Q hcover hroot hQ hmin fixed hfixed
      exact of_decide_eq_true ((List.all_eq_true.mp hh.1) _ (List.get_mem ..))
    · simpa using hcard
  | split b absent present ih0 ih1 =>
    have hh : absent.check columns K Q ((b,false)::fixed) = true ∧
        present.check columns K Q ((b,true)::fixed) = true := by
      simpa only [CoverTree.check,Bool.and_eq_true] using checked
    by_cases hb : b ∈ outsideCodes F
    · apply ih1 _ hh.2
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [hb]
      · exact hfixed x hx
    · apply ih0 _ hh.1
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [hb]
      · exact hfixed x hx

end C13.Enumeration.Census
