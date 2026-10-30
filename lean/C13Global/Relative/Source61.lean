import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source61
import C13Global.FastGroups.Source61Part00
import C13Global.FastGroups.Source61Part01
namespace C13.Global.Relative.Source61
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source61
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link61 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link61 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link61 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link61 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link61 alphabets) :
    ActualObstruction link61 FastDual61_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link61 rootCodes root_binding alphabets halph nonincident_complete
    FastDual61_000.pointList FastDual61_000.columns FastDual61_000.rows FastDual61_000.bound (by decide +kernel)
    FastDual61_000.column_mask FastDual61_000.checked hc F hF hroot hmin hout

theorem query217 (halph : AlphabetComplete link61 alphabets) : ActualObstruction link61 {1,3,6,10} := rep000 halph

theorem rep001 (halph : AlphabetComplete link61 alphabets) :
    ActualObstruction link61 FastDual61_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link61 rootCodes root_binding alphabets halph nonincident_complete
    FastDual61_001.pointList FastDual61_001.columns FastDual61_001.rows FastDual61_001.bound (by decide +kernel)
    FastDual61_001.column_mask FastDual61_001.checked hc F hF hroot hmin hout

theorem query218 (halph : AlphabetComplete link61 alphabets) : ActualObstruction link61 {1,3,6,11} := rep001 halph

theorem rep002 (halph : AlphabetComplete link61 alphabets) :
    ActualObstruction link61 FastDual61_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link61 rootCodes root_binding alphabets halph nonincident_complete
    FastDual61_002.pointList FastDual61_002.columns FastDual61_002.rows FastDual61_002.bound (by decide +kernel)
    FastDual61_002.column_mask FastDual61_002.checked hc F hF hroot hmin hout

theorem query221 (halph : AlphabetComplete link61 alphabets) : ActualObstruction link61 {1,3,7,10} := rep002 halph

theorem rep003 (halph : AlphabetComplete link61 alphabets) :
    ActualObstruction link61 FastDual61_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link61 rootCodes root_binding alphabets halph nonincident_complete
    FastDual61_003.pointList FastDual61_003.columns FastDual61_003.rows FastDual61_003.bound (by decide +kernel)
    FastDual61_003.column_mask FastDual61_003.checked hc F hF hroot hmin hout

theorem query222 (halph : AlphabetComplete link61 alphabets) : ActualObstruction link61 {1,3,7,11} := rep003 halph

theorem rep004 (halph : AlphabetComplete link61 alphabets) :
    ActualObstruction link61 FastDual61_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link61 rootCodes root_binding alphabets halph nonincident_complete
    FastDual61_004.pointList FastDual61_004.columns FastDual61_004.rows FastDual61_004.bound (by decide +kernel)
    FastDual61_004.column_mask FastDual61_004.checked hc F hF hroot hmin hout

theorem query267 (halph : AlphabetComplete link61 alphabets) : ActualObstruction link61 {1,6,7,10} := rep004 halph

theorem rep005 (halph : AlphabetComplete link61 alphabets) :
    ActualObstruction link61 FastDual61_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link61 rootCodes root_binding alphabets halph nonincident_complete
    FastDual61_005.pointList FastDual61_005.columns FastDual61_005.rows FastDual61_005.bound (by decide +kernel)
    FastDual61_005.column_mask FastDual61_005.checked hc F hF hroot hmin hout

theorem query268 (halph : AlphabetComplete link61 alphabets) : ActualObstruction link61 {1,6,7,11} := rep005 halph

theorem rep006 (halph : AlphabetComplete link61 alphabets) :
    ActualObstruction link61 FastDual61_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link61 rootCodes root_binding alphabets halph nonincident_complete
    FastDual61_006.pointList FastDual61_006.columns FastDual61_006.rows FastDual61_006.bound (by decide +kernel)
    FastDual61_006.column_mask FastDual61_006.checked hc F hF hroot hmin hout

theorem query274 (halph : AlphabetComplete link61 alphabets) : ActualObstruction link61 {1,6,10,11} := rep006 halph

theorem rep007 (halph : AlphabetComplete link61 alphabets) :
    ActualObstruction link61 FastDual61_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link61 rootCodes root_binding alphabets halph nonincident_complete
    FastDual61_007.pointList FastDual61_007.columns FastDual61_007.rows FastDual61_007.bound (by decide +kernel)
    FastDual61_007.column_mask FastDual61_007.checked hc F hF hroot hmin hout

theorem query280 (halph : AlphabetComplete link61 alphabets) : ActualObstruction link61 {1,7,10,11} := rep007 halph

theorem rep008 (halph : AlphabetComplete link61 alphabets) :
    ActualObstruction link61 FastDual61_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link61 rootCodes root_binding alphabets halph nonincident_complete
    FastDual61_008.pointList FastDual61_008.columns FastDual61_008.rows FastDual61_008.bound (by decide +kernel)
    FastDual61_008.column_mask FastDual61_008.checked hc F hF hroot hmin hout

theorem query407 (halph : AlphabetComplete link61 alphabets) : ActualObstruction link61 {3,6,7,10} := rep008 halph

theorem rep009 (halph : AlphabetComplete link61 alphabets) :
    ActualObstruction link61 FastDual61_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link61 rootCodes root_binding alphabets halph nonincident_complete
    FastDual61_009.pointList FastDual61_009.columns FastDual61_009.rows FastDual61_009.bound (by decide +kernel)
    FastDual61_009.column_mask FastDual61_009.checked hc F hF hroot hmin hout

theorem query408 (halph : AlphabetComplete link61 alphabets) : ActualObstruction link61 {3,6,7,11} := rep009 halph

theorem rep010 (halph : AlphabetComplete link61 alphabets) :
    ActualObstruction link61 FastDual61_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link61 rootCodes root_binding alphabets halph nonincident_complete
    FastDual61_010.pointList FastDual61_010.columns FastDual61_010.rows FastDual61_010.bound (by decide +kernel)
    FastDual61_010.column_mask FastDual61_010.checked hc F hF hroot hmin hout

theorem query414 (halph : AlphabetComplete link61 alphabets) : ActualObstruction link61 {3,6,10,11} := rep010 halph

theorem rep011 (halph : AlphabetComplete link61 alphabets) :
    ActualObstruction link61 FastDual61_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link61 rootCodes root_binding alphabets halph nonincident_complete
    FastDual61_011.pointList FastDual61_011.columns FastDual61_011.rows FastDual61_011.bound (by decide +kernel)
    FastDual61_011.column_mask FastDual61_011.checked hc F hF hroot hmin hout

theorem query420 (halph : AlphabetComplete link61 alphabets) : ActualObstruction link61 {3,7,10,11} := rep011 halph

theorem rep012 (halph : AlphabetComplete link61 alphabets) :
    ActualObstruction link61 FastDual61_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link61 rootCodes root_binding alphabets halph nonincident_complete
    FastDual61_012.pointList FastDual61_012.columns FastDual61_012.rows FastDual61_012.bound (by decide +kernel)
    FastDual61_012.column_mask FastDual61_012.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link61 alphabets) : ActualObstruction link61 {6,7,10,11} := rep012 halph

def dualQuads : List (Finset Point) := [{1,3,6,10},{1,3,6,11},{1,3,7,10},{1,3,7,11},{1,6,7,10},{1,6,7,11},{1,6,10,11},{1,7,10,11},{3,6,7,10},{3,6,7,11},{3,6,10,11},{3,7,10,11},{6,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link61 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link61 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query217 halph
  · exact query218 halph
  · exact query221 halph
  · exact query222 halph
  · exact query267 halph
  · exact query268 halph
  · exact query274 halph
  · exact query280 halph
  · exact query407 halph
  · exact query408 halph
  · exact query414 halph
  · exact query420 halph
  · exact query485 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link61 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link61 Q :=
  class_census link61 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source61
