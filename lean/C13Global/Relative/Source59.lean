import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source59
import C13Global.FastGroups.Source59Part00
import C13Global.FastGroups.Source59Part01
namespace C13.Global.Relative.Source59
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source59
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link59 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link59 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link59 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link59 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link59 alphabets) :
    ActualObstruction link59 FastDual59_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link59 rootCodes root_binding alphabets halph nonincident_complete
    FastDual59_000.pointList FastDual59_000.columns FastDual59_000.rows FastDual59_000.bound (by decide +kernel)
    FastDual59_000.column_mask FastDual59_000.checked hc F hF hroot hmin hout

theorem query296 (halph : AlphabetComplete link59 alphabets) : ActualObstruction link59 {2,3,5,10} := rep000 halph

theorem rep001 (halph : AlphabetComplete link59 alphabets) :
    ActualObstruction link59 FastDual59_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link59 rootCodes root_binding alphabets halph nonincident_complete
    FastDual59_001.pointList FastDual59_001.columns FastDual59_001.rows FastDual59_001.bound (by decide +kernel)
    FastDual59_001.column_mask FastDual59_001.checked hc F hF hroot hmin hout

theorem query297 (halph : AlphabetComplete link59 alphabets) : ActualObstruction link59 {2,3,5,11} := rep001 halph

theorem rep002 (halph : AlphabetComplete link59 alphabets) :
    ActualObstruction link59 FastDual59_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link59 rootCodes root_binding alphabets halph nonincident_complete
    FastDual59_002.pointList FastDual59_002.columns FastDual59_002.rows FastDual59_002.bound (by decide +kernel)
    FastDual59_002.column_mask FastDual59_002.checked hc F hF hroot hmin hout

theorem query305 (halph : AlphabetComplete link59 alphabets) : ActualObstruction link59 {2,3,7,10} := rep002 halph

theorem rep003 (halph : AlphabetComplete link59 alphabets) :
    ActualObstruction link59 FastDual59_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link59 rootCodes root_binding alphabets halph nonincident_complete
    FastDual59_003.pointList FastDual59_003.columns FastDual59_003.rows FastDual59_003.bound (by decide +kernel)
    FastDual59_003.column_mask FastDual59_003.checked hc F hF hroot hmin hout

theorem query306 (halph : AlphabetComplete link59 alphabets) : ActualObstruction link59 {2,3,7,11} := rep003 halph

theorem rep004 (halph : AlphabetComplete link59 alphabets) :
    ActualObstruction link59 FastDual59_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link59 rootCodes root_binding alphabets halph nonincident_complete
    FastDual59_004.pointList FastDual59_004.columns FastDual59_004.rows FastDual59_004.bound (by decide +kernel)
    FastDual59_004.column_mask FastDual59_004.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link59 alphabets) : ActualObstruction link59 {2,3,10,11} := rep004 halph

theorem rep005 (halph : AlphabetComplete link59 alphabets) :
    ActualObstruction link59 FastDual59_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link59 rootCodes root_binding alphabets halph nonincident_complete
    FastDual59_005.pointList FastDual59_005.columns FastDual59_005.rows FastDual59_005.bound (by decide +kernel)
    FastDual59_005.column_mask FastDual59_005.checked hc F hF hroot hmin hout

theorem query341 (halph : AlphabetComplete link59 alphabets) : ActualObstruction link59 {2,5,7,10} := rep005 halph

theorem rep006 (halph : AlphabetComplete link59 alphabets) :
    ActualObstruction link59 FastDual59_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link59 rootCodes root_binding alphabets halph nonincident_complete
    FastDual59_006.pointList FastDual59_006.columns FastDual59_006.rows FastDual59_006.bound (by decide +kernel)
    FastDual59_006.column_mask FastDual59_006.checked hc F hF hroot hmin hout

theorem query342 (halph : AlphabetComplete link59 alphabets) : ActualObstruction link59 {2,5,7,11} := rep006 halph

theorem rep007 (halph : AlphabetComplete link59 alphabets) :
    ActualObstruction link59 FastDual59_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link59 rootCodes root_binding alphabets halph nonincident_complete
    FastDual59_007.pointList FastDual59_007.columns FastDual59_007.rows FastDual59_007.bound (by decide +kernel)
    FastDual59_007.column_mask FastDual59_007.checked hc F hF hroot hmin hout

theorem query348 (halph : AlphabetComplete link59 alphabets) : ActualObstruction link59 {2,5,10,11} := rep007 halph

theorem rep008 (halph : AlphabetComplete link59 alphabets) :
    ActualObstruction link59 FastDual59_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link59 rootCodes root_binding alphabets halph nonincident_complete
    FastDual59_008.pointList FastDual59_008.columns FastDual59_008.rows FastDual59_008.bound (by decide +kernel)
    FastDual59_008.column_mask FastDual59_008.checked hc F hF hroot hmin hout

theorem query364 (halph : AlphabetComplete link59 alphabets) : ActualObstruction link59 {2,7,10,11} := rep008 halph

theorem rep009 (halph : AlphabetComplete link59 alphabets) :
    ActualObstruction link59 FastDual59_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link59 rootCodes root_binding alphabets halph nonincident_complete
    FastDual59_009.pointList FastDual59_009.columns FastDual59_009.rows FastDual59_009.bound (by decide +kernel)
    FastDual59_009.column_mask FastDual59_009.checked hc F hF hroot hmin hout

theorem query397 (halph : AlphabetComplete link59 alphabets) : ActualObstruction link59 {3,5,7,10} := rep009 halph

theorem rep010 (halph : AlphabetComplete link59 alphabets) :
    ActualObstruction link59 FastDual59_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link59 rootCodes root_binding alphabets halph nonincident_complete
    FastDual59_010.pointList FastDual59_010.columns FastDual59_010.rows FastDual59_010.bound (by decide +kernel)
    FastDual59_010.column_mask FastDual59_010.checked hc F hF hroot hmin hout

theorem query398 (halph : AlphabetComplete link59 alphabets) : ActualObstruction link59 {3,5,7,11} := rep010 halph

theorem rep011 (halph : AlphabetComplete link59 alphabets) :
    ActualObstruction link59 FastDual59_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link59 rootCodes root_binding alphabets halph nonincident_complete
    FastDual59_011.pointList FastDual59_011.columns FastDual59_011.rows FastDual59_011.bound (by decide +kernel)
    FastDual59_011.column_mask FastDual59_011.checked hc F hF hroot hmin hout

theorem query404 (halph : AlphabetComplete link59 alphabets) : ActualObstruction link59 {3,5,10,11} := rep011 halph

theorem rep012 (halph : AlphabetComplete link59 alphabets) :
    ActualObstruction link59 FastDual59_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link59 rootCodes root_binding alphabets halph nonincident_complete
    FastDual59_012.pointList FastDual59_012.columns FastDual59_012.rows FastDual59_012.bound (by decide +kernel)
    FastDual59_012.column_mask FastDual59_012.checked hc F hF hroot hmin hout

theorem query420 (halph : AlphabetComplete link59 alphabets) : ActualObstruction link59 {3,7,10,11} := rep012 halph

def dualQuads : List (Finset Point) := [{2,3,5,10},{2,3,5,11},{2,3,7,10},{2,3,7,11},{2,3,10,11},{2,5,7,10},{2,5,7,11},{2,5,10,11},{2,7,10,11},{3,5,7,10},{3,5,7,11},{3,5,10,11},{3,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link59 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link59 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query296 halph
  · exact query297 halph
  · exact query305 halph
  · exact query306 halph
  · exact query312 halph
  · exact query341 halph
  · exact query342 halph
  · exact query348 halph
  · exact query364 halph
  · exact query397 halph
  · exact query398 halph
  · exact query404 halph
  · exact query420 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link59 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link59 Q :=
  class_census link59 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source59
