import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source23
import C13Global.FastGroups.Source23Part00
import C13Global.FastGroups.Source23Part01
namespace C13.Global.Relative.Source23
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source23
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link23 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link23 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link23 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link23 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link23 alphabets) :
    ActualObstruction link23 FastDual23_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link23 rootCodes root_binding alphabets halph nonincident_complete
    FastDual23_000.pointList FastDual23_000.columns FastDual23_000.rows FastDual23_000.bound (by decide +kernel)
    FastDual23_000.column_mask FastDual23_000.checked hc F hF hroot hmin hout

theorem query406 (halph : AlphabetComplete link23 alphabets) : ActualObstruction link23 {3,6,7,9} := rep000 halph

theorem rep001 (halph : AlphabetComplete link23 alphabets) :
    ActualObstruction link23 FastDual23_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link23 rootCodes root_binding alphabets halph nonincident_complete
    FastDual23_001.pointList FastDual23_001.columns FastDual23_001.rows FastDual23_001.bound (by decide +kernel)
    FastDual23_001.column_mask FastDual23_001.checked hc F hF hroot hmin hout

theorem query407 (halph : AlphabetComplete link23 alphabets) : ActualObstruction link23 {3,6,7,10} := rep001 halph

theorem rep002 (halph : AlphabetComplete link23 alphabets) :
    ActualObstruction link23 FastDual23_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link23 rootCodes root_binding alphabets halph nonincident_complete
    FastDual23_002.pointList FastDual23_002.columns FastDual23_002.rows FastDual23_002.bound (by decide +kernel)
    FastDual23_002.column_mask FastDual23_002.checked hc F hF hroot hmin hout

theorem query408 (halph : AlphabetComplete link23 alphabets) : ActualObstruction link23 {3,6,7,11} := rep002 halph

theorem rep003 (halph : AlphabetComplete link23 alphabets) :
    ActualObstruction link23 FastDual23_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link23 rootCodes root_binding alphabets halph nonincident_complete
    FastDual23_003.pointList FastDual23_003.columns FastDual23_003.rows FastDual23_003.bound (by decide +kernel)
    FastDual23_003.column_mask FastDual23_003.checked hc F hF hroot hmin hout

theorem query412 (halph : AlphabetComplete link23 alphabets) : ActualObstruction link23 {3,6,9,10} := rep003 halph

theorem rep004 (halph : AlphabetComplete link23 alphabets) :
    ActualObstruction link23 FastDual23_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link23 rootCodes root_binding alphabets halph nonincident_complete
    FastDual23_004.pointList FastDual23_004.columns FastDual23_004.rows FastDual23_004.bound (by decide +kernel)
    FastDual23_004.column_mask FastDual23_004.checked hc F hF hroot hmin hout

theorem query413 (halph : AlphabetComplete link23 alphabets) : ActualObstruction link23 {3,6,9,11} := rep004 halph

theorem rep005 (halph : AlphabetComplete link23 alphabets) :
    ActualObstruction link23 FastDual23_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link23 rootCodes root_binding alphabets halph nonincident_complete
    FastDual23_005.pointList FastDual23_005.columns FastDual23_005.rows FastDual23_005.bound (by decide +kernel)
    FastDual23_005.column_mask FastDual23_005.checked hc F hF hroot hmin hout

theorem query414 (halph : AlphabetComplete link23 alphabets) : ActualObstruction link23 {3,6,10,11} := rep005 halph

theorem rep006 (halph : AlphabetComplete link23 alphabets) :
    ActualObstruction link23 FastDual23_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link23 rootCodes root_binding alphabets halph nonincident_complete
    FastDual23_006.pointList FastDual23_006.columns FastDual23_006.rows FastDual23_006.bound (by decide +kernel)
    FastDual23_006.column_mask FastDual23_006.checked hc F hF hroot hmin hout

theorem query418 (halph : AlphabetComplete link23 alphabets) : ActualObstruction link23 {3,7,9,10} := rep006 halph

theorem rep007 (halph : AlphabetComplete link23 alphabets) :
    ActualObstruction link23 FastDual23_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link23 rootCodes root_binding alphabets halph nonincident_complete
    FastDual23_007.pointList FastDual23_007.columns FastDual23_007.rows FastDual23_007.bound (by decide +kernel)
    FastDual23_007.column_mask FastDual23_007.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link23 alphabets) : ActualObstruction link23 {3,7,9,11} := rep007 halph

theorem rep008 (halph : AlphabetComplete link23 alphabets) :
    ActualObstruction link23 FastDual23_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link23 rootCodes root_binding alphabets halph nonincident_complete
    FastDual23_008.pointList FastDual23_008.columns FastDual23_008.rows FastDual23_008.bound (by decide +kernel)
    FastDual23_008.column_mask FastDual23_008.checked hc F hF hroot hmin hout

theorem query420 (halph : AlphabetComplete link23 alphabets) : ActualObstruction link23 {3,7,10,11} := rep008 halph

theorem rep009 (halph : AlphabetComplete link23 alphabets) :
    ActualObstruction link23 FastDual23_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link23 rootCodes root_binding alphabets halph nonincident_complete
    FastDual23_009.pointList FastDual23_009.columns FastDual23_009.rows FastDual23_009.bound (by decide +kernel)
    FastDual23_009.column_mask FastDual23_009.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link23 alphabets) : ActualObstruction link23 {6,7,10,11} := rep009 halph

def dualQuads : List (Finset Point) := [{3,6,7,9},{3,6,7,10},{3,6,7,11},{3,6,9,10},{3,6,9,11},{3,6,10,11},{3,7,9,10},{3,7,9,11},{3,7,10,11},{6,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link23 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link23 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query406 halph
  · exact query407 halph
  · exact query408 halph
  · exact query412 halph
  · exact query413 halph
  · exact query414 halph
  · exact query418 halph
  · exact query419 halph
  · exact query420 halph
  · exact query485 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link23 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link23 Q :=
  class_census link23 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source23
