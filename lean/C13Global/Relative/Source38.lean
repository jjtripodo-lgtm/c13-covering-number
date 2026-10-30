import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source38
import C13Global.FastGroups.Source38Part00
import C13Global.FastGroups.Source38Part01
import C13Global.FastGroups.Source38Part02
namespace C13.Global.Relative.Source38
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source38
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link38 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link38 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link38 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link38 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_000.pointList FastDual38_000.columns FastDual38_000.rows FastDual38_000.bound (by decide +kernel)
    FastDual38_000.column_mask FastDual38_000.checked hc F hF hroot hmin hout

theorem query192 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {1,2,7,9} := rep000 halph

theorem rep001 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_001.pointList FastDual38_001.columns FastDual38_001.rows FastDual38_001.bound (by decide +kernel)
    FastDual38_001.column_mask FastDual38_001.checked hc F hF hroot hmin hout

theorem query193 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {1,2,7,10} := rep001 halph

theorem rep002 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_002.pointList FastDual38_002.columns FastDual38_002.rows FastDual38_002.bound (by decide +kernel)
    FastDual38_002.column_mask FastDual38_002.checked hc F hF hroot hmin hout

theorem query194 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {1,2,7,11} := rep002 halph

theorem rep003 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_003.pointList FastDual38_003.columns FastDual38_003.rows FastDual38_003.bound (by decide +kernel)
    FastDual38_003.column_mask FastDual38_003.checked hc F hF hroot hmin hout

theorem query198 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {1,2,9,10} := rep003 halph

theorem rep004 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_004.pointList FastDual38_004.columns FastDual38_004.rows FastDual38_004.bound (by decide +kernel)
    FastDual38_004.column_mask FastDual38_004.checked hc F hF hroot hmin hout

theorem query220 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {1,3,7,9} := rep004 halph

theorem rep005 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_005.pointList FastDual38_005.columns FastDual38_005.rows FastDual38_005.bound (by decide +kernel)
    FastDual38_005.column_mask FastDual38_005.checked hc F hF hroot hmin hout

theorem query221 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {1,3,7,10} := rep005 halph

theorem rep006 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_006.pointList FastDual38_006.columns FastDual38_006.rows FastDual38_006.bound (by decide +kernel)
    FastDual38_006.column_mask FastDual38_006.checked hc F hF hroot hmin hout

theorem query222 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {1,3,7,11} := rep006 halph

theorem rep007 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_007.pointList FastDual38_007.columns FastDual38_007.rows FastDual38_007.bound (by decide +kernel)
    FastDual38_007.column_mask FastDual38_007.checked hc F hF hroot hmin hout

theorem query227 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {1,3,9,11} := rep007 halph

theorem rep008 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_008.pointList FastDual38_008.columns FastDual38_008.rows FastDual38_008.bound (by decide +kernel)
    FastDual38_008.column_mask FastDual38_008.checked hc F hF hroot hmin hout

theorem query278 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {1,7,9,10} := rep008 halph

theorem rep009 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_009.pointList FastDual38_009.columns FastDual38_009.rows FastDual38_009.bound (by decide +kernel)
    FastDual38_009.column_mask FastDual38_009.checked hc F hF hroot hmin hout

theorem query279 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {1,7,9,11} := rep009 halph

theorem rep010 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_010.pointList FastDual38_010.columns FastDual38_010.rows FastDual38_010.bound (by decide +kernel)
    FastDual38_010.column_mask FastDual38_010.checked hc F hF hroot hmin hout

theorem query280 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {1,7,10,11} := rep010 halph

theorem rep011 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_011.pointList FastDual38_011.columns FastDual38_011.rows FastDual38_011.bound (by decide +kernel)
    FastDual38_011.column_mask FastDual38_011.checked hc F hF hroot hmin hout

theorem query304 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {2,3,7,9} := rep011 halph

theorem rep012 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_012.pointList FastDual38_012.columns FastDual38_012.rows FastDual38_012.bound (by decide +kernel)
    FastDual38_012.column_mask FastDual38_012.checked hc F hF hroot hmin hout

theorem query305 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {2,3,7,10} := rep012 halph

theorem rep013 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_013.pointList FastDual38_013.columns FastDual38_013.rows FastDual38_013.bound (by decide +kernel)
    FastDual38_013.column_mask FastDual38_013.checked hc F hF hroot hmin hout

theorem query306 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {2,3,7,11} := rep013 halph

theorem rep014 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_014.pointList FastDual38_014.columns FastDual38_014.rows FastDual38_014.bound (by decide +kernel)
    FastDual38_014.column_mask FastDual38_014.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {2,3,10,11} := rep014 halph

theorem rep015 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_015.pointList FastDual38_015.columns FastDual38_015.rows FastDual38_015.bound (by decide +kernel)
    FastDual38_015.column_mask FastDual38_015.checked hc F hF hroot hmin hout

theorem query362 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {2,7,9,10} := rep015 halph

theorem rep016 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_016.pointList FastDual38_016.columns FastDual38_016.rows FastDual38_016.bound (by decide +kernel)
    FastDual38_016.column_mask FastDual38_016.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {2,7,9,11} := rep016 halph

theorem rep017 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_017.pointList FastDual38_017.columns FastDual38_017.rows FastDual38_017.bound (by decide +kernel)
    FastDual38_017.column_mask FastDual38_017.checked hc F hF hroot hmin hout

theorem query364 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {2,7,10,11} := rep017 halph

theorem rep018 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_018.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_018.pointList FastDual38_018.columns FastDual38_018.rows FastDual38_018.bound (by decide +kernel)
    FastDual38_018.column_mask FastDual38_018.checked hc F hF hroot hmin hout

theorem query418 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {3,7,9,10} := rep018 halph

theorem rep019 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_019.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_019.pointList FastDual38_019.columns FastDual38_019.rows FastDual38_019.bound (by decide +kernel)
    FastDual38_019.column_mask FastDual38_019.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {3,7,9,11} := rep019 halph

theorem rep020 (halph : AlphabetComplete link38 alphabets) :
    ActualObstruction link38 FastDual38_020.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link38 rootCodes root_binding alphabets halph nonincident_complete
    FastDual38_020.pointList FastDual38_020.columns FastDual38_020.rows FastDual38_020.bound (by decide +kernel)
    FastDual38_020.column_mask FastDual38_020.checked hc F hF hroot hmin hout

theorem query420 (halph : AlphabetComplete link38 alphabets) : ActualObstruction link38 {3,7,10,11} := rep020 halph

def dualQuads : List (Finset Point) := [{1,2,7,9},{1,2,7,10},{1,2,7,11},{1,2,9,10},{1,3,7,9},{1,3,7,10},{1,3,7,11},{1,3,9,11},{1,7,9,10},{1,7,9,11},{1,7,10,11},{2,3,7,9},{2,3,7,10},{2,3,7,11},{2,3,10,11},{2,7,9,10},{2,7,9,11},{2,7,10,11},{3,7,9,10},{3,7,9,11},{3,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link38 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link38 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query192 halph
  · exact query193 halph
  · exact query194 halph
  · exact query198 halph
  · exact query220 halph
  · exact query221 halph
  · exact query222 halph
  · exact query227 halph
  · exact query278 halph
  · exact query279 halph
  · exact query280 halph
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

theorem all_foursets (halph : AlphabetComplete link38 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link38 Q :=
  class_census link38 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source38
