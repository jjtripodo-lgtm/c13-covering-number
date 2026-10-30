import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source48
import C13Global.FastGroups.Source48Part00
import C13Global.FastGroups.Source48Part01
namespace C13.Global.Relative.Source48
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source48
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link48 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link48 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link48 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link48 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link48 alphabets) :
    ActualObstruction link48 FastDual48_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link48 rootCodes root_binding alphabets halph nonincident_complete
    FastDual48_000.pointList FastDual48_000.columns FastDual48_000.rows FastDual48_000.bound (by decide +kernel)
    FastDual48_000.column_mask FastDual48_000.checked hc F hF hroot hmin hout

theorem query219 (halph : AlphabetComplete link48 alphabets) : ActualObstruction link48 {1,3,7,8} := rep000 halph

theorem rep001 (halph : AlphabetComplete link48 alphabets) :
    ActualObstruction link48 FastDual48_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link48 rootCodes root_binding alphabets halph nonincident_complete
    FastDual48_001.pointList FastDual48_001.columns FastDual48_001.rows FastDual48_001.bound (by decide +kernel)
    FastDual48_001.column_mask FastDual48_001.checked hc F hF hroot hmin hout

theorem query220 (halph : AlphabetComplete link48 alphabets) : ActualObstruction link48 {1,3,7,9} := rep001 halph

theorem rep002 (halph : AlphabetComplete link48 alphabets) :
    ActualObstruction link48 FastDual48_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link48 rootCodes root_binding alphabets halph nonincident_complete
    FastDual48_002.pointList FastDual48_002.columns FastDual48_002.rows FastDual48_002.bound (by decide +kernel)
    FastDual48_002.column_mask FastDual48_002.checked hc F hF hroot hmin hout

theorem query222 (halph : AlphabetComplete link48 alphabets) : ActualObstruction link48 {1,3,7,11} := rep002 halph

theorem rep003 (halph : AlphabetComplete link48 alphabets) :
    ActualObstruction link48 FastDual48_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link48 rootCodes root_binding alphabets halph nonincident_complete
    FastDual48_003.pointList FastDual48_003.columns FastDual48_003.rows FastDual48_003.bound (by decide +kernel)
    FastDual48_003.column_mask FastDual48_003.checked hc F hF hroot hmin hout

theorem query227 (halph : AlphabetComplete link48 alphabets) : ActualObstruction link48 {1,3,9,11} := rep003 halph

theorem rep004 (halph : AlphabetComplete link48 alphabets) :
    ActualObstruction link48 FastDual48_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link48 rootCodes root_binding alphabets halph nonincident_complete
    FastDual48_004.pointList FastDual48_004.columns FastDual48_004.rows FastDual48_004.bound (by decide +kernel)
    FastDual48_004.column_mask FastDual48_004.checked hc F hF hroot hmin hout

theorem query275 (halph : AlphabetComplete link48 alphabets) : ActualObstruction link48 {1,7,8,9} := rep004 halph

theorem rep005 (halph : AlphabetComplete link48 alphabets) :
    ActualObstruction link48 FastDual48_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link48 rootCodes root_binding alphabets halph nonincident_complete
    FastDual48_005.pointList FastDual48_005.columns FastDual48_005.rows FastDual48_005.bound (by decide +kernel)
    FastDual48_005.column_mask FastDual48_005.checked hc F hF hroot hmin hout

theorem query277 (halph : AlphabetComplete link48 alphabets) : ActualObstruction link48 {1,7,8,11} := rep005 halph

theorem rep006 (halph : AlphabetComplete link48 alphabets) :
    ActualObstruction link48 FastDual48_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link48 rootCodes root_binding alphabets halph nonincident_complete
    FastDual48_006.pointList FastDual48_006.columns FastDual48_006.rows FastDual48_006.bound (by decide +kernel)
    FastDual48_006.column_mask FastDual48_006.checked hc F hF hroot hmin hout

theorem query279 (halph : AlphabetComplete link48 alphabets) : ActualObstruction link48 {1,7,9,11} := rep006 halph

theorem rep007 (halph : AlphabetComplete link48 alphabets) :
    ActualObstruction link48 FastDual48_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link48 rootCodes root_binding alphabets halph nonincident_complete
    FastDual48_007.pointList FastDual48_007.columns FastDual48_007.rows FastDual48_007.bound (by decide +kernel)
    FastDual48_007.column_mask FastDual48_007.checked hc F hF hroot hmin hout

theorem query415 (halph : AlphabetComplete link48 alphabets) : ActualObstruction link48 {3,7,8,9} := rep007 halph

theorem rep008 (halph : AlphabetComplete link48 alphabets) :
    ActualObstruction link48 FastDual48_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link48 rootCodes root_binding alphabets halph nonincident_complete
    FastDual48_008.pointList FastDual48_008.columns FastDual48_008.rows FastDual48_008.bound (by decide +kernel)
    FastDual48_008.column_mask FastDual48_008.checked hc F hF hroot hmin hout

theorem query417 (halph : AlphabetComplete link48 alphabets) : ActualObstruction link48 {3,7,8,11} := rep008 halph

theorem rep009 (halph : AlphabetComplete link48 alphabets) :
    ActualObstruction link48 FastDual48_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link48 rootCodes root_binding alphabets halph nonincident_complete
    FastDual48_009.pointList FastDual48_009.columns FastDual48_009.rows FastDual48_009.bound (by decide +kernel)
    FastDual48_009.column_mask FastDual48_009.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link48 alphabets) : ActualObstruction link48 {3,7,9,11} := rep009 halph

def dualQuads : List (Finset Point) := [{1,3,7,8},{1,3,7,9},{1,3,7,11},{1,3,9,11},{1,7,8,9},{1,7,8,11},{1,7,9,11},{3,7,8,9},{3,7,8,11},{3,7,9,11}]

theorem dual_actual (halph : AlphabetComplete link48 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link48 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query219 halph
  · exact query220 halph
  · exact query222 halph
  · exact query227 halph
  · exact query275 halph
  · exact query277 halph
  · exact query279 halph
  · exact query415 halph
  · exact query417 halph
  · exact query419 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link48 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link48 Q :=
  class_census link48 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source48
