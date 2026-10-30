import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source28
import C13Global.FastGroups.Source28Part00
import C13Global.FastGroups.Source28Part01
import C13Global.FastGroups.Source28Part02
namespace C13.Global.Relative.Source28
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source28
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link28 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link28 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link28 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link28 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_000.pointList FastDual28_000.columns FastDual28_000.rows FastDual28_000.bound (by decide +kernel)
    FastDual28_000.column_mask FastDual28_000.checked hc F hF hroot hmin hout

theorem query171 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {1,2,3,10} := rep000 halph

theorem rep001 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_001.pointList FastDual28_001.columns FastDual28_001.rows FastDual28_001.bound (by decide +kernel)
    FastDual28_001.column_mask FastDual28_001.checked hc F hF hroot hmin hout

theorem query192 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {1,2,7,9} := rep001 halph

theorem rep002 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_002.pointList FastDual28_002.columns FastDual28_002.rows FastDual28_002.bound (by decide +kernel)
    FastDual28_002.column_mask FastDual28_002.checked hc F hF hroot hmin hout

theorem query193 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {1,2,7,10} := rep002 halph

theorem rep003 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_003.pointList FastDual28_003.columns FastDual28_003.rows FastDual28_003.bound (by decide +kernel)
    FastDual28_003.column_mask FastDual28_003.checked hc F hF hroot hmin hout

theorem query194 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {1,2,7,11} := rep003 halph

theorem rep004 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_004.pointList FastDual28_004.columns FastDual28_004.rows FastDual28_004.bound (by decide +kernel)
    FastDual28_004.column_mask FastDual28_004.checked hc F hF hroot hmin hout

theorem query198 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {1,2,9,10} := rep004 halph

theorem rep005 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_005.pointList FastDual28_005.columns FastDual28_005.rows FastDual28_005.bound (by decide +kernel)
    FastDual28_005.column_mask FastDual28_005.checked hc F hF hroot hmin hout

theorem query220 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {1,3,7,9} := rep005 halph

theorem rep006 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_006.pointList FastDual28_006.columns FastDual28_006.rows FastDual28_006.bound (by decide +kernel)
    FastDual28_006.column_mask FastDual28_006.checked hc F hF hroot hmin hout

theorem query221 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {1,3,7,10} := rep006 halph

theorem rep007 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_007.pointList FastDual28_007.columns FastDual28_007.rows FastDual28_007.bound (by decide +kernel)
    FastDual28_007.column_mask FastDual28_007.checked hc F hF hroot hmin hout

theorem query222 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {1,3,7,11} := rep007 halph

theorem rep008 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_008.pointList FastDual28_008.columns FastDual28_008.rows FastDual28_008.bound (by decide +kernel)
    FastDual28_008.column_mask FastDual28_008.checked hc F hF hroot hmin hout

theorem query227 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {1,3,9,11} := rep008 halph

theorem rep009 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_009.pointList FastDual28_009.columns FastDual28_009.rows FastDual28_009.bound (by decide +kernel)
    FastDual28_009.column_mask FastDual28_009.checked hc F hF hroot hmin hout

theorem query278 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {1,7,9,10} := rep009 halph

theorem rep010 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_010.pointList FastDual28_010.columns FastDual28_010.rows FastDual28_010.bound (by decide +kernel)
    FastDual28_010.column_mask FastDual28_010.checked hc F hF hroot hmin hout

theorem query279 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {1,7,9,11} := rep010 halph

theorem rep011 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_011.pointList FastDual28_011.columns FastDual28_011.rows FastDual28_011.bound (by decide +kernel)
    FastDual28_011.column_mask FastDual28_011.checked hc F hF hroot hmin hout

theorem query280 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {1,7,10,11} := rep011 halph

theorem rep012 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_012.pointList FastDual28_012.columns FastDual28_012.rows FastDual28_012.bound (by decide +kernel)
    FastDual28_012.column_mask FastDual28_012.checked hc F hF hroot hmin hout

theorem query304 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {2,3,7,9} := rep012 halph

theorem rep013 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_013.pointList FastDual28_013.columns FastDual28_013.rows FastDual28_013.bound (by decide +kernel)
    FastDual28_013.column_mask FastDual28_013.checked hc F hF hroot hmin hout

theorem query305 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {2,3,7,10} := rep013 halph

theorem rep014 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_014.pointList FastDual28_014.columns FastDual28_014.rows FastDual28_014.bound (by decide +kernel)
    FastDual28_014.column_mask FastDual28_014.checked hc F hF hroot hmin hout

theorem query306 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {2,3,7,11} := rep014 halph

theorem rep015 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_015.pointList FastDual28_015.columns FastDual28_015.rows FastDual28_015.bound (by decide +kernel)
    FastDual28_015.column_mask FastDual28_015.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {2,3,10,11} := rep015 halph

theorem rep016 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_016.pointList FastDual28_016.columns FastDual28_016.rows FastDual28_016.bound (by decide +kernel)
    FastDual28_016.column_mask FastDual28_016.checked hc F hF hroot hmin hout

theorem query362 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {2,7,9,10} := rep016 halph

theorem rep017 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_017.pointList FastDual28_017.columns FastDual28_017.rows FastDual28_017.bound (by decide +kernel)
    FastDual28_017.column_mask FastDual28_017.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {2,7,9,11} := rep017 halph

theorem rep018 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_018.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_018.pointList FastDual28_018.columns FastDual28_018.rows FastDual28_018.bound (by decide +kernel)
    FastDual28_018.column_mask FastDual28_018.checked hc F hF hroot hmin hout

theorem query364 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {2,7,10,11} := rep018 halph

theorem rep019 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_019.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_019.pointList FastDual28_019.columns FastDual28_019.rows FastDual28_019.bound (by decide +kernel)
    FastDual28_019.column_mask FastDual28_019.checked hc F hF hroot hmin hout

theorem query418 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {3,7,9,10} := rep019 halph

theorem rep020 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_020.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_020.pointList FastDual28_020.columns FastDual28_020.rows FastDual28_020.bound (by decide +kernel)
    FastDual28_020.column_mask FastDual28_020.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {3,7,9,11} := rep020 halph

theorem rep021 (halph : AlphabetComplete link28 alphabets) :
    ActualObstruction link28 FastDual28_021.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link28 rootCodes root_binding alphabets halph nonincident_complete
    FastDual28_021.pointList FastDual28_021.columns FastDual28_021.rows FastDual28_021.bound (by decide +kernel)
    FastDual28_021.column_mask FastDual28_021.checked hc F hF hroot hmin hout

theorem query420 (halph : AlphabetComplete link28 alphabets) : ActualObstruction link28 {3,7,10,11} := rep021 halph

def dualQuads : List (Finset Point) := [{1,2,3,10},{1,2,7,9},{1,2,7,10},{1,2,7,11},{1,2,9,10},{1,3,7,9},{1,3,7,10},{1,3,7,11},{1,3,9,11},{1,7,9,10},{1,7,9,11},{1,7,10,11},{2,3,7,9},{2,3,7,10},{2,3,7,11},{2,3,10,11},{2,7,9,10},{2,7,9,11},{2,7,10,11},{3,7,9,10},{3,7,9,11},{3,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link28 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link28 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query171 halph
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

theorem all_foursets (halph : AlphabetComplete link28 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link28 Q :=
  class_census link28 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source28
