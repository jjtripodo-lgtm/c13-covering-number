import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source49
import C13Global.FastGroups.Source49Part00
import C13Global.FastGroups.Source49Part01
namespace C13.Global.Relative.Source49
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source49
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link49 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link49 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link49 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link49 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link49 alphabets) :
    ActualObstruction link49 FastDual49_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link49 rootCodes root_binding alphabets halph nonincident_complete
    FastDual49_000.pointList FastDual49_000.columns FastDual49_000.rows FastDual49_000.bound (by decide +kernel)
    FastDual49_000.column_mask FastDual49_000.checked hc F hF hroot hmin hout

theorem query215 (halph : AlphabetComplete link49 alphabets) : ActualObstruction link49 {1,3,6,8} := rep000 halph

theorem rep001 (halph : AlphabetComplete link49 alphabets) :
    ActualObstruction link49 FastDual49_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link49 rootCodes root_binding alphabets halph nonincident_complete
    FastDual49_001.pointList FastDual49_001.columns FastDual49_001.rows FastDual49_001.bound (by decide +kernel)
    FastDual49_001.column_mask FastDual49_001.checked hc F hF hroot hmin hout

theorem query216 (halph : AlphabetComplete link49 alphabets) : ActualObstruction link49 {1,3,6,9} := rep001 halph

theorem rep002 (halph : AlphabetComplete link49 alphabets) :
    ActualObstruction link49 FastDual49_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link49 rootCodes root_binding alphabets halph nonincident_complete
    FastDual49_002.pointList FastDual49_002.columns FastDual49_002.rows FastDual49_002.bound (by decide +kernel)
    FastDual49_002.column_mask FastDual49_002.checked hc F hF hroot hmin hout

theorem query218 (halph : AlphabetComplete link49 alphabets) : ActualObstruction link49 {1,3,6,11} := rep002 halph

theorem rep003 (halph : AlphabetComplete link49 alphabets) :
    ActualObstruction link49 FastDual49_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link49 rootCodes root_binding alphabets halph nonincident_complete
    FastDual49_003.pointList FastDual49_003.columns FastDual49_003.rows FastDual49_003.bound (by decide +kernel)
    FastDual49_003.column_mask FastDual49_003.checked hc F hF hroot hmin hout

theorem query227 (halph : AlphabetComplete link49 alphabets) : ActualObstruction link49 {1,3,9,11} := rep003 halph

theorem rep004 (halph : AlphabetComplete link49 alphabets) :
    ActualObstruction link49 FastDual49_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link49 rootCodes root_binding alphabets halph nonincident_complete
    FastDual49_004.pointList FastDual49_004.columns FastDual49_004.rows FastDual49_004.bound (by decide +kernel)
    FastDual49_004.column_mask FastDual49_004.checked hc F hF hroot hmin hout

theorem query269 (halph : AlphabetComplete link49 alphabets) : ActualObstruction link49 {1,6,8,9} := rep004 halph

theorem rep005 (halph : AlphabetComplete link49 alphabets) :
    ActualObstruction link49 FastDual49_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link49 rootCodes root_binding alphabets halph nonincident_complete
    FastDual49_005.pointList FastDual49_005.columns FastDual49_005.rows FastDual49_005.bound (by decide +kernel)
    FastDual49_005.column_mask FastDual49_005.checked hc F hF hroot hmin hout

theorem query271 (halph : AlphabetComplete link49 alphabets) : ActualObstruction link49 {1,6,8,11} := rep005 halph

theorem rep006 (halph : AlphabetComplete link49 alphabets) :
    ActualObstruction link49 FastDual49_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link49 rootCodes root_binding alphabets halph nonincident_complete
    FastDual49_006.pointList FastDual49_006.columns FastDual49_006.rows FastDual49_006.bound (by decide +kernel)
    FastDual49_006.column_mask FastDual49_006.checked hc F hF hroot hmin hout

theorem query273 (halph : AlphabetComplete link49 alphabets) : ActualObstruction link49 {1,6,9,11} := rep006 halph

theorem rep007 (halph : AlphabetComplete link49 alphabets) :
    ActualObstruction link49 FastDual49_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link49 rootCodes root_binding alphabets halph nonincident_complete
    FastDual49_007.pointList FastDual49_007.columns FastDual49_007.rows FastDual49_007.bound (by decide +kernel)
    FastDual49_007.column_mask FastDual49_007.checked hc F hF hroot hmin hout

theorem query409 (halph : AlphabetComplete link49 alphabets) : ActualObstruction link49 {3,6,8,9} := rep007 halph

theorem rep008 (halph : AlphabetComplete link49 alphabets) :
    ActualObstruction link49 FastDual49_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link49 rootCodes root_binding alphabets halph nonincident_complete
    FastDual49_008.pointList FastDual49_008.columns FastDual49_008.rows FastDual49_008.bound (by decide +kernel)
    FastDual49_008.column_mask FastDual49_008.checked hc F hF hroot hmin hout

theorem query411 (halph : AlphabetComplete link49 alphabets) : ActualObstruction link49 {3,6,8,11} := rep008 halph

theorem rep009 (halph : AlphabetComplete link49 alphabets) :
    ActualObstruction link49 FastDual49_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link49 rootCodes root_binding alphabets halph nonincident_complete
    FastDual49_009.pointList FastDual49_009.columns FastDual49_009.rows FastDual49_009.bound (by decide +kernel)
    FastDual49_009.column_mask FastDual49_009.checked hc F hF hroot hmin hout

theorem query413 (halph : AlphabetComplete link49 alphabets) : ActualObstruction link49 {3,6,9,11} := rep009 halph

theorem rep010 (halph : AlphabetComplete link49 alphabets) :
    ActualObstruction link49 FastDual49_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link49 rootCodes root_binding alphabets halph nonincident_complete
    FastDual49_010.pointList FastDual49_010.columns FastDual49_010.rows FastDual49_010.bound (by decide +kernel)
    FastDual49_010.column_mask FastDual49_010.checked hc F hF hroot hmin hout

theorem query487 (halph : AlphabetComplete link49 alphabets) : ActualObstruction link49 {6,8,9,11} := rep010 halph

def dualQuads : List (Finset Point) := [{1,3,6,8},{1,3,6,9},{1,3,6,11},{1,3,9,11},{1,6,8,9},{1,6,8,11},{1,6,9,11},{3,6,8,9},{3,6,8,11},{3,6,9,11},{6,8,9,11}]

theorem dual_actual (halph : AlphabetComplete link49 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link49 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query215 halph
  · exact query216 halph
  · exact query218 halph
  · exact query227 halph
  · exact query269 halph
  · exact query271 halph
  · exact query273 halph
  · exact query409 halph
  · exact query411 halph
  · exact query413 halph
  · exact query487 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link49 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link49 Q :=
  class_census link49 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source49
