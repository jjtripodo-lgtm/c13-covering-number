import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source24
import C13Global.FastGroups.Source24Part00
import C13Global.FastGroups.Source24Part01
namespace C13.Global.Relative.Source24
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source24
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link24 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link24 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link24 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link24 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link24 alphabets) :
    ActualObstruction link24 FastDual24_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link24 rootCodes root_binding alphabets halph nonincident_complete
    FastDual24_000.pointList FastDual24_000.columns FastDual24_000.rows FastDual24_000.bound (by decide +kernel)
    FastDual24_000.column_mask FastDual24_000.checked hc F hF hroot hmin hout

theorem query405 (halph : AlphabetComplete link24 alphabets) : ActualObstruction link24 {3,6,7,8} := rep000 halph

theorem rep001 (halph : AlphabetComplete link24 alphabets) :
    ActualObstruction link24 FastDual24_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link24 rootCodes root_binding alphabets halph nonincident_complete
    FastDual24_001.pointList FastDual24_001.columns FastDual24_001.rows FastDual24_001.bound (by decide +kernel)
    FastDual24_001.column_mask FastDual24_001.checked hc F hF hroot hmin hout

theorem query406 (halph : AlphabetComplete link24 alphabets) : ActualObstruction link24 {3,6,7,9} := rep001 halph

theorem rep002 (halph : AlphabetComplete link24 alphabets) :
    ActualObstruction link24 FastDual24_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link24 rootCodes root_binding alphabets halph nonincident_complete
    FastDual24_002.pointList FastDual24_002.columns FastDual24_002.rows FastDual24_002.bound (by decide +kernel)
    FastDual24_002.column_mask FastDual24_002.checked hc F hF hroot hmin hout

theorem query408 (halph : AlphabetComplete link24 alphabets) : ActualObstruction link24 {3,6,7,11} := rep002 halph

theorem rep003 (halph : AlphabetComplete link24 alphabets) :
    ActualObstruction link24 FastDual24_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link24 rootCodes root_binding alphabets halph nonincident_complete
    FastDual24_003.pointList FastDual24_003.columns FastDual24_003.rows FastDual24_003.bound (by decide +kernel)
    FastDual24_003.column_mask FastDual24_003.checked hc F hF hroot hmin hout

theorem query409 (halph : AlphabetComplete link24 alphabets) : ActualObstruction link24 {3,6,8,9} := rep003 halph

theorem rep004 (halph : AlphabetComplete link24 alphabets) :
    ActualObstruction link24 FastDual24_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link24 rootCodes root_binding alphabets halph nonincident_complete
    FastDual24_004.pointList FastDual24_004.columns FastDual24_004.rows FastDual24_004.bound (by decide +kernel)
    FastDual24_004.column_mask FastDual24_004.checked hc F hF hroot hmin hout

theorem query411 (halph : AlphabetComplete link24 alphabets) : ActualObstruction link24 {3,6,8,11} := rep004 halph

theorem rep005 (halph : AlphabetComplete link24 alphabets) :
    ActualObstruction link24 FastDual24_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link24 rootCodes root_binding alphabets halph nonincident_complete
    FastDual24_005.pointList FastDual24_005.columns FastDual24_005.rows FastDual24_005.bound (by decide +kernel)
    FastDual24_005.column_mask FastDual24_005.checked hc F hF hroot hmin hout

theorem query413 (halph : AlphabetComplete link24 alphabets) : ActualObstruction link24 {3,6,9,11} := rep005 halph

theorem rep006 (halph : AlphabetComplete link24 alphabets) :
    ActualObstruction link24 FastDual24_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link24 rootCodes root_binding alphabets halph nonincident_complete
    FastDual24_006.pointList FastDual24_006.columns FastDual24_006.rows FastDual24_006.bound (by decide +kernel)
    FastDual24_006.column_mask FastDual24_006.checked hc F hF hroot hmin hout

theorem query415 (halph : AlphabetComplete link24 alphabets) : ActualObstruction link24 {3,7,8,9} := rep006 halph

theorem rep007 (halph : AlphabetComplete link24 alphabets) :
    ActualObstruction link24 FastDual24_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link24 rootCodes root_binding alphabets halph nonincident_complete
    FastDual24_007.pointList FastDual24_007.columns FastDual24_007.rows FastDual24_007.bound (by decide +kernel)
    FastDual24_007.column_mask FastDual24_007.checked hc F hF hroot hmin hout

theorem query417 (halph : AlphabetComplete link24 alphabets) : ActualObstruction link24 {3,7,8,11} := rep007 halph

theorem rep008 (halph : AlphabetComplete link24 alphabets) :
    ActualObstruction link24 FastDual24_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link24 rootCodes root_binding alphabets halph nonincident_complete
    FastDual24_008.pointList FastDual24_008.columns FastDual24_008.rows FastDual24_008.bound (by decide +kernel)
    FastDual24_008.column_mask FastDual24_008.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link24 alphabets) : ActualObstruction link24 {3,7,9,11} := rep008 halph

theorem rep009 (halph : AlphabetComplete link24 alphabets) :
    ActualObstruction link24 FastDual24_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link24 rootCodes root_binding alphabets halph nonincident_complete
    FastDual24_009.pointList FastDual24_009.columns FastDual24_009.rows FastDual24_009.bound (by decide +kernel)
    FastDual24_009.column_mask FastDual24_009.checked hc F hF hroot hmin hout

theorem query480 (halph : AlphabetComplete link24 alphabets) : ActualObstruction link24 {6,7,8,9} := rep009 halph

theorem rep010 (halph : AlphabetComplete link24 alphabets) :
    ActualObstruction link24 FastDual24_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link24 rootCodes root_binding alphabets halph nonincident_complete
    FastDual24_010.pointList FastDual24_010.columns FastDual24_010.rows FastDual24_010.bound (by decide +kernel)
    FastDual24_010.column_mask FastDual24_010.checked hc F hF hroot hmin hout

theorem query491 (halph : AlphabetComplete link24 alphabets) : ActualObstruction link24 {7,8,9,11} := rep010 halph

def dualQuads : List (Finset Point) := [{3,6,7,8},{3,6,7,9},{3,6,7,11},{3,6,8,9},{3,6,8,11},{3,6,9,11},{3,7,8,9},{3,7,8,11},{3,7,9,11},{6,7,8,9},{7,8,9,11}]

theorem dual_actual (halph : AlphabetComplete link24 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link24 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query405 halph
  · exact query406 halph
  · exact query408 halph
  · exact query409 halph
  · exact query411 halph
  · exact query413 halph
  · exact query415 halph
  · exact query417 halph
  · exact query419 halph
  · exact query480 halph
  · exact query491 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link24 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link24 Q :=
  class_census link24 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source24
