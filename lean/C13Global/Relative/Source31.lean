import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source31
import C13Global.FastGroups.Source31Part00
import C13Global.FastGroups.Source31Part01
namespace C13.Global.Relative.Source31
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source31
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link31 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link31 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link31 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link31 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link31 alphabets) :
    ActualObstruction link31 FastDual31_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link31 rootCodes root_binding alphabets halph nonincident_complete
    FastDual31_000.pointList FastDual31_000.columns FastDual31_000.rows FastDual31_000.bound (by decide +kernel)
    FastDual31_000.column_mask FastDual31_000.checked hc F hF hroot hmin hout

theorem query304 (halph : AlphabetComplete link31 alphabets) : ActualObstruction link31 {2,3,7,9} := rep000 halph

theorem rep001 (halph : AlphabetComplete link31 alphabets) :
    ActualObstruction link31 FastDual31_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link31 rootCodes root_binding alphabets halph nonincident_complete
    FastDual31_001.pointList FastDual31_001.columns FastDual31_001.rows FastDual31_001.bound (by decide +kernel)
    FastDual31_001.column_mask FastDual31_001.checked hc F hF hroot hmin hout

theorem query305 (halph : AlphabetComplete link31 alphabets) : ActualObstruction link31 {2,3,7,10} := rep001 halph

theorem rep002 (halph : AlphabetComplete link31 alphabets) :
    ActualObstruction link31 FastDual31_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link31 rootCodes root_binding alphabets halph nonincident_complete
    FastDual31_002.pointList FastDual31_002.columns FastDual31_002.rows FastDual31_002.bound (by decide +kernel)
    FastDual31_002.column_mask FastDual31_002.checked hc F hF hroot hmin hout

theorem query306 (halph : AlphabetComplete link31 alphabets) : ActualObstruction link31 {2,3,7,11} := rep002 halph

theorem rep003 (halph : AlphabetComplete link31 alphabets) :
    ActualObstruction link31 FastDual31_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link31 rootCodes root_binding alphabets halph nonincident_complete
    FastDual31_003.pointList FastDual31_003.columns FastDual31_003.rows FastDual31_003.bound (by decide +kernel)
    FastDual31_003.column_mask FastDual31_003.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link31 alphabets) : ActualObstruction link31 {2,3,10,11} := rep003 halph

theorem rep004 (halph : AlphabetComplete link31 alphabets) :
    ActualObstruction link31 FastDual31_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link31 rootCodes root_binding alphabets halph nonincident_complete
    FastDual31_004.pointList FastDual31_004.columns FastDual31_004.rows FastDual31_004.bound (by decide +kernel)
    FastDual31_004.column_mask FastDual31_004.checked hc F hF hroot hmin hout

theorem query362 (halph : AlphabetComplete link31 alphabets) : ActualObstruction link31 {2,7,9,10} := rep004 halph

theorem rep005 (halph : AlphabetComplete link31 alphabets) :
    ActualObstruction link31 FastDual31_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link31 rootCodes root_binding alphabets halph nonincident_complete
    FastDual31_005.pointList FastDual31_005.columns FastDual31_005.rows FastDual31_005.bound (by decide +kernel)
    FastDual31_005.column_mask FastDual31_005.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link31 alphabets) : ActualObstruction link31 {2,7,9,11} := rep005 halph

theorem rep006 (halph : AlphabetComplete link31 alphabets) :
    ActualObstruction link31 FastDual31_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link31 rootCodes root_binding alphabets halph nonincident_complete
    FastDual31_006.pointList FastDual31_006.columns FastDual31_006.rows FastDual31_006.bound (by decide +kernel)
    FastDual31_006.column_mask FastDual31_006.checked hc F hF hroot hmin hout

theorem query364 (halph : AlphabetComplete link31 alphabets) : ActualObstruction link31 {2,7,10,11} := rep006 halph

theorem rep007 (halph : AlphabetComplete link31 alphabets) :
    ActualObstruction link31 FastDual31_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link31 rootCodes root_binding alphabets halph nonincident_complete
    FastDual31_007.pointList FastDual31_007.columns FastDual31_007.rows FastDual31_007.bound (by decide +kernel)
    FastDual31_007.column_mask FastDual31_007.checked hc F hF hroot hmin hout

theorem query418 (halph : AlphabetComplete link31 alphabets) : ActualObstruction link31 {3,7,9,10} := rep007 halph

theorem rep008 (halph : AlphabetComplete link31 alphabets) :
    ActualObstruction link31 FastDual31_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link31 rootCodes root_binding alphabets halph nonincident_complete
    FastDual31_008.pointList FastDual31_008.columns FastDual31_008.rows FastDual31_008.bound (by decide +kernel)
    FastDual31_008.column_mask FastDual31_008.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link31 alphabets) : ActualObstruction link31 {3,7,9,11} := rep008 halph

theorem rep009 (halph : AlphabetComplete link31 alphabets) :
    ActualObstruction link31 FastDual31_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link31 rootCodes root_binding alphabets halph nonincident_complete
    FastDual31_009.pointList FastDual31_009.columns FastDual31_009.rows FastDual31_009.bound (by decide +kernel)
    FastDual31_009.column_mask FastDual31_009.checked hc F hF hroot hmin hout

theorem query420 (halph : AlphabetComplete link31 alphabets) : ActualObstruction link31 {3,7,10,11} := rep009 halph

def dualQuads : List (Finset Point) := [{2,3,7,9},{2,3,7,10},{2,3,7,11},{2,3,10,11},{2,7,9,10},{2,7,9,11},{2,7,10,11},{3,7,9,10},{3,7,9,11},{3,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link31 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link31 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query304 halph
  · exact query305 halph
  · exact query306 halph
  · exact query312 halph
  · exact query362 halph
  · exact query363 halph
  · exact query364 halph
  · exact query418 halph
  · exact query419 halph
  · exact query420 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link31 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link31 Q :=
  class_census link31 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source31
