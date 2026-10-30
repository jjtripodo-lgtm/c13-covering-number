import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source05
import C13Global.FastGroups.Source05Part00
namespace C13.Global.Relative.Source05
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source05
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link05 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link05 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link05 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link05 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link05 alphabets) :
    ActualObstruction link05 FastDual05_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link05 rootCodes root_binding alphabets halph nonincident_complete
    FastDual05_000.pointList FastDual05_000.columns FastDual05_000.rows FastDual05_000.bound (by decide +kernel)
    FastDual05_000.column_mask FastDual05_000.checked hc F hF hroot hmin hout

theorem query480 (halph : AlphabetComplete link05 alphabets) : ActualObstruction link05 {6,7,8,9} := rep000 halph

theorem rep001 (halph : AlphabetComplete link05 alphabets) :
    ActualObstruction link05 FastDual05_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link05 rootCodes root_binding alphabets halph nonincident_complete
    FastDual05_001.pointList FastDual05_001.columns FastDual05_001.rows FastDual05_001.bound (by decide +kernel)
    FastDual05_001.column_mask FastDual05_001.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link05 alphabets) : ActualObstruction link05 {6,7,10,11} := rep001 halph

theorem rep002 (halph : AlphabetComplete link05 alphabets) :
    ActualObstruction link05 FastDual05_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link05 rootCodes root_binding alphabets halph nonincident_complete
    FastDual05_002.pointList FastDual05_002.columns FastDual05_002.rows FastDual05_002.bound (by decide +kernel)
    FastDual05_002.column_mask FastDual05_002.checked hc F hF hroot hmin hout

theorem query494 (halph : AlphabetComplete link05 alphabets) : ActualObstruction link05 {8,9,10,11} := rep002 halph

def dualQuads : List (Finset Point) := [{6,7,8,9},{6,7,10,11},{8,9,10,11}]

theorem dual_actual (halph : AlphabetComplete link05 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link05 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl
  · exact query480 halph
  · exact query485 halph
  · exact query494 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link05 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link05 Q :=
  class_census link05 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source05
