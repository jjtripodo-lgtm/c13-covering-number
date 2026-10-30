import C13Global.Irredundance
import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source18
import C13Global.FastGroups.Source18Part00
import C13Global.FastGroups.Source18Part01
import C13Global.FastGroups.Source18Part02
namespace C13.Global.Relative.Source18
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source18
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link18 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link18 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link18 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link18 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_000.pointList FastDual18_000.columns FastDual18_000.rows FastDual18_000.bound (by decide +kernel)
    FastDual18_000.column_mask FastDual18_000.checked hc F hF hroot hmin hout

theorem query219 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {1,3,7,8} := rep000 halph

theorem rep001 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_001.pointList FastDual18_001.columns FastDual18_001.rows FastDual18_001.bound (by decide +kernel)
    FastDual18_001.column_mask FastDual18_001.checked hc F hF hroot hmin hout

theorem query220 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {1,3,7,9} := rep001 halph

theorem rep002 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_002.pointList FastDual18_002.columns FastDual18_002.rows FastDual18_002.bound (by decide +kernel)
    FastDual18_002.column_mask FastDual18_002.checked hc F hF hroot hmin hout

theorem query221 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {1,3,7,10} := rep002 halph

theorem rep003 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_003.pointList FastDual18_003.columns FastDual18_003.rows FastDual18_003.bound (by decide +kernel)
    FastDual18_003.column_mask FastDual18_003.checked hc F hF hroot hmin hout

theorem query222 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {1,3,7,11} := rep003 halph

theorem rep004 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_004.pointList FastDual18_004.columns FastDual18_004.rows FastDual18_004.bound (by decide +kernel)
    FastDual18_004.column_mask FastDual18_004.checked hc F hF hroot hmin hout

theorem query224 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {1,3,8,10} := rep004 halph

theorem rep005 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_005.pointList FastDual18_005.columns FastDual18_005.rows FastDual18_005.bound (by decide +kernel)
    FastDual18_005.column_mask FastDual18_005.checked hc F hF hroot hmin hout

theorem query227 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {1,3,9,11} := rep005 halph

theorem rep006 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_006.pointList FastDual18_006.columns FastDual18_006.rows FastDual18_006.bound (by decide +kernel)
    FastDual18_006.column_mask FastDual18_006.checked hc F hF hroot hmin hout

theorem query275 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {1,7,8,9} := rep006 halph

theorem rep007 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_007.pointList FastDual18_007.columns FastDual18_007.rows FastDual18_007.bound (by decide +kernel)
    FastDual18_007.column_mask FastDual18_007.checked hc F hF hroot hmin hout

theorem query276 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {1,7,8,10} := rep007 halph

theorem rep008 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_008.pointList FastDual18_008.columns FastDual18_008.rows FastDual18_008.bound (by decide +kernel)
    FastDual18_008.column_mask FastDual18_008.checked hc F hF hroot hmin hout

theorem query277 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {1,7,8,11} := rep008 halph

theorem rep009 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_009.pointList FastDual18_009.columns FastDual18_009.rows FastDual18_009.bound (by decide +kernel)
    FastDual18_009.column_mask FastDual18_009.checked hc F hF hroot hmin hout

theorem query278 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {1,7,9,10} := rep009 halph

theorem rep010 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_010.pointList FastDual18_010.columns FastDual18_010.rows FastDual18_010.bound (by decide +kernel)
    FastDual18_010.column_mask FastDual18_010.checked hc F hF hroot hmin hout

theorem query279 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {1,7,9,11} := rep010 halph

theorem rep011 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_011.pointList FastDual18_011.columns FastDual18_011.rows FastDual18_011.bound (by decide +kernel)
    FastDual18_011.column_mask FastDual18_011.checked hc F hF hroot hmin hout

theorem query280 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {1,7,10,11} := rep011 halph

theorem rep012 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_012.pointList FastDual18_012.columns FastDual18_012.rows FastDual18_012.bound (by decide +kernel)
    FastDual18_012.column_mask FastDual18_012.checked hc F hF hroot hmin hout

theorem query415 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {3,7,8,9} := rep012 halph

theorem rep013 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_013.pointList FastDual18_013.columns FastDual18_013.rows FastDual18_013.bound (by decide +kernel)
    FastDual18_013.column_mask FastDual18_013.checked hc F hF hroot hmin hout

theorem query416 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {3,7,8,10} := rep013 halph

theorem rep014 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_014.pointList FastDual18_014.columns FastDual18_014.rows FastDual18_014.bound (by decide +kernel)
    FastDual18_014.column_mask FastDual18_014.checked hc F hF hroot hmin hout

theorem query417 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {3,7,8,11} := rep014 halph

theorem rep015 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_015.pointList FastDual18_015.columns FastDual18_015.rows FastDual18_015.bound (by decide +kernel)
    FastDual18_015.column_mask FastDual18_015.checked hc F hF hroot hmin hout

theorem query418 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {3,7,9,10} := rep015 halph

theorem rep016 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_016.pointList FastDual18_016.columns FastDual18_016.rows FastDual18_016.bound (by decide +kernel)
    FastDual18_016.column_mask FastDual18_016.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {3,7,9,11} := rep016 halph

theorem rep017 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_017.pointList FastDual18_017.columns FastDual18_017.rows FastDual18_017.bound (by decide +kernel)
    FastDual18_017.column_mask FastDual18_017.checked hc F hF hroot hmin hout

theorem query420 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {3,7,10,11} := rep017 halph

theorem rep018 (halph : AlphabetComplete link18 alphabets) :
    ActualObstruction link18 FastDual18_018.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link18 rootCodes root_binding alphabets halph nonincident_complete
    FastDual18_018.pointList FastDual18_018.columns FastDual18_018.rows FastDual18_018.bound (by decide +kernel)
    FastDual18_018.column_mask FastDual18_018.checked hc F hF hroot hmin hout

theorem query494 (halph : AlphabetComplete link18 alphabets) : ActualObstruction link18 {8,9,10,11} := rep018 halph

def dualQuads : List (Finset Point) := [{1,3,7,8},{1,3,7,9},{1,3,7,10},{1,3,7,11},{1,3,8,10},{1,3,9,11},{1,7,8,9},{1,7,8,10},{1,7,8,11},{1,7,9,10},{1,7,9,11},{1,7,10,11},{3,7,8,9},{3,7,8,10},{3,7,8,11},{3,7,9,10},{3,7,9,11},{3,7,10,11},{8,9,10,11}]

theorem dual_actual (halph : AlphabetComplete link18 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link18 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query219 halph
  · exact query220 halph
  · exact query221 halph
  · exact query222 halph
  · exact query224 halph
  · exact query227 halph
  · exact query275 halph
  · exact query276 halph
  · exact query277 halph
  · exact query278 halph
  · exact query279 halph
  · exact query280 halph
  · exact query415 halph
  · exact query416 halph
  · exact query417 halph
  · exact query418 halph
  · exact query419 halph
  · exact query420 halph
  · exact query494 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link18 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link18 Q :=
  class_census link18 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source18
