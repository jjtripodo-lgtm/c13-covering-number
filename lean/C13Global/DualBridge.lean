import C13Global.Physical
import C13Global.RawDual
import C13Global.RowValidity

namespace C13.Global
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem rawValidRow_valid (K : Family Point) (Q : Finset Point) (r : LinearRow)
    (h : RawValidRow K Q r) : ValidRow K Q [] r := by
  cases ht : r.test <;> simp_all [RawValidRow,ValidRow]

theorem rawLeafCheck_sound (columns : List Code) (K : Family Point)
    (Q : Finset Point) (rows : List LinearRow) (bound : Int)
    (checked : rawLeafCheck columns K Q rows bound = true)
    (F : Family Point) (hcover : IsCoverOn univ F 7 4) (hroot : link F hole = K)
    (hQ : Q ⊆ univ.erase hole) (hmin : ∀ q ∈ Q, degree F q = 15)
    (hcolumns : ∀ b ∈ outsideCodes F, b ∈ columns)
    (hcard : (outside F hole).card ≤ 14) : False := by
  have hh : rows.all (fun r => decide (RawValidRow K Q r)) = true ∧
      certificateB columns rows bound 14 = true := by
    simpa only [rawLeafCheck,Bool.and_eq_true] using checked
  apply certificate_sound columns rows bound 14 hh.2 (outsideCodes F) hcolumns
  · intro i
    apply valid_row_satisfied F K Q hcover hroot hQ hmin [] (by simp [FixedHolds])
    exact rawValidRow_valid K Q _ (of_decide_eq_true (List.all_eq_true.mp hh.1 _ (List.get_mem ..)))
  · simpa using hcard

theorem dual_actual_obstruction (K : Family Point) (alphabets : List Mask)
    (halph : AlphabetComplete K alphabets) (hnon : NonincidentComplete alphabets)
    (points : List Point) (columns : List Code) (rows : List LinearRow) (bound : Int)
    (hpoints : ∀ q ∈ points, q ≠ hole)
    (column_mask : listMask columns = restrictMask universeMask alphabets points)
    (checked : rawLeafCheck columns K points.toFinset rows bound = true)
    (hclass : ClassifiesMinimumLinks catalog hole)
    (F : Family Point) (hcover : IsCoverOn univ F 7 4) (hroot : link F hole = K)
    (hmin : ∀ q ∈ points.toFinset, degree F q = 15)
    (hcard : (outside F hole).card ≤ 14) : False := by
  apply rawLeafCheck_sound columns K points.toFinset rows bound checked F hcover hroot
    (by intro q hq; exact mem_erase.mpr ⟨hpoints q (List.mem_toFinset.mp hq),mem_univ _⟩)
    hmin _ hcard
  intro b hb
  obtain ⟨B,hB,rfl⟩ := mem_image.mp hb
  apply mem_of_mask_eq columns _ column_mask
  apply restrictMask_bit
  · rw [← universeMask_checked,listMask_bit]
    exact decide_eq_true (blockUniverse_complete F hcover B hB)
  · intro q hq
    exact actual_support K alphabets halph hnon hclass F hcover hroot q
      (hpoints q hq) (hmin q (List.mem_toFinset.mpr hq)) B hB

end C13.Global
