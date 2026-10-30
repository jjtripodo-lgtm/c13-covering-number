import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source34
import C13Global.FastGroups.Source34Part00
import C13Global.FastGroups.Source34Part01
namespace C13.Global.Relative.Source34
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source34
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link34 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link34 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link34 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link34 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link34 alphabets) :
    ActualObstruction link34 FastDual34_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link34 rootCodes root_binding alphabets halph nonincident_complete
    FastDual34_000.pointList FastDual34_000.columns FastDual34_000.rows FastDual34_000.bound (by decide +kernel)
    FastDual34_000.column_mask FastDual34_000.checked hc F hF hroot hmin hout

theorem query220 (halph : AlphabetComplete link34 alphabets) : ActualObstruction link34 {1,3,7,9} := rep000 halph

theorem rep001 (halph : AlphabetComplete link34 alphabets) :
    ActualObstruction link34 FastDual34_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link34 rootCodes root_binding alphabets halph nonincident_complete
    FastDual34_001.pointList FastDual34_001.columns FastDual34_001.rows FastDual34_001.bound (by decide +kernel)
    FastDual34_001.column_mask FastDual34_001.checked hc F hF hroot hmin hout

theorem query221 (halph : AlphabetComplete link34 alphabets) : ActualObstruction link34 {1,3,7,10} := rep001 halph

theorem rep002 (halph : AlphabetComplete link34 alphabets) :
    ActualObstruction link34 FastDual34_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link34 rootCodes root_binding alphabets halph nonincident_complete
    FastDual34_002.pointList FastDual34_002.columns FastDual34_002.rows FastDual34_002.bound (by decide +kernel)
    FastDual34_002.column_mask FastDual34_002.checked hc F hF hroot hmin hout

theorem query222 (halph : AlphabetComplete link34 alphabets) : ActualObstruction link34 {1,3,7,11} := rep002 halph

theorem rep003 (halph : AlphabetComplete link34 alphabets) :
    ActualObstruction link34 FastDual34_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link34 rootCodes root_binding alphabets halph nonincident_complete
    FastDual34_003.pointList FastDual34_003.columns FastDual34_003.rows FastDual34_003.bound (by decide +kernel)
    FastDual34_003.column_mask FastDual34_003.checked hc F hF hroot hmin hout

theorem query227 (halph : AlphabetComplete link34 alphabets) : ActualObstruction link34 {1,3,9,11} := rep003 halph

theorem rep004 (halph : AlphabetComplete link34 alphabets) :
    ActualObstruction link34 FastDual34_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link34 rootCodes root_binding alphabets halph nonincident_complete
    FastDual34_004.pointList FastDual34_004.columns FastDual34_004.rows FastDual34_004.bound (by decide +kernel)
    FastDual34_004.column_mask FastDual34_004.checked hc F hF hroot hmin hout

theorem query278 (halph : AlphabetComplete link34 alphabets) : ActualObstruction link34 {1,7,9,10} := rep004 halph

theorem rep005 (halph : AlphabetComplete link34 alphabets) :
    ActualObstruction link34 FastDual34_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link34 rootCodes root_binding alphabets halph nonincident_complete
    FastDual34_005.pointList FastDual34_005.columns FastDual34_005.rows FastDual34_005.bound (by decide +kernel)
    FastDual34_005.column_mask FastDual34_005.checked hc F hF hroot hmin hout

theorem query279 (halph : AlphabetComplete link34 alphabets) : ActualObstruction link34 {1,7,9,11} := rep005 halph

theorem rep006 (halph : AlphabetComplete link34 alphabets) :
    ActualObstruction link34 FastDual34_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link34 rootCodes root_binding alphabets halph nonincident_complete
    FastDual34_006.pointList FastDual34_006.columns FastDual34_006.rows FastDual34_006.bound (by decide +kernel)
    FastDual34_006.column_mask FastDual34_006.checked hc F hF hroot hmin hout

theorem query280 (halph : AlphabetComplete link34 alphabets) : ActualObstruction link34 {1,7,10,11} := rep006 halph

theorem rep007 (halph : AlphabetComplete link34 alphabets) :
    ActualObstruction link34 FastDual34_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link34 rootCodes root_binding alphabets halph nonincident_complete
    FastDual34_007.pointList FastDual34_007.columns FastDual34_007.rows FastDual34_007.bound (by decide +kernel)
    FastDual34_007.column_mask FastDual34_007.checked hc F hF hroot hmin hout

theorem query418 (halph : AlphabetComplete link34 alphabets) : ActualObstruction link34 {3,7,9,10} := rep007 halph

theorem rep008 (halph : AlphabetComplete link34 alphabets) :
    ActualObstruction link34 FastDual34_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link34 rootCodes root_binding alphabets halph nonincident_complete
    FastDual34_008.pointList FastDual34_008.columns FastDual34_008.rows FastDual34_008.bound (by decide +kernel)
    FastDual34_008.column_mask FastDual34_008.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link34 alphabets) : ActualObstruction link34 {3,7,9,11} := rep008 halph

theorem rep009 (halph : AlphabetComplete link34 alphabets) :
    ActualObstruction link34 FastDual34_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link34 rootCodes root_binding alphabets halph nonincident_complete
    FastDual34_009.pointList FastDual34_009.columns FastDual34_009.rows FastDual34_009.bound (by decide +kernel)
    FastDual34_009.column_mask FastDual34_009.checked hc F hF hroot hmin hout

theorem query420 (halph : AlphabetComplete link34 alphabets) : ActualObstruction link34 {3,7,10,11} := rep009 halph

def dualQuads : List (Finset Point) := [{1,3,7,9},{1,3,7,10},{1,3,7,11},{1,3,9,11},{1,7,9,10},{1,7,9,11},{1,7,10,11},{3,7,9,10},{3,7,9,11},{3,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link34 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link34 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query220 halph
  · exact query221 halph
  · exact query222 halph
  · exact query227 halph
  · exact query278 halph
  · exact query279 halph
  · exact query280 halph
  · exact query418 halph
  · exact query419 halph
  · exact query420 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link34 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link34 Q :=
  class_census link34 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source34
