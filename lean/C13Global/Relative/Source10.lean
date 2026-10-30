import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source10
import C13Global.FastGroups.Source10Part00
namespace C13.Global.Relative.Source10
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source10
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link10 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link10 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link10 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link10 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link10 alphabets) :
    ActualObstruction link10 FastDual10_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link10 rootCodes root_binding alphabets halph nonincident_complete
    FastDual10_000.pointList FastDual10_000.columns FastDual10_000.rows FastDual10_000.bound (by decide +kernel)
    FastDual10_000.column_mask FastDual10_000.checked hc F hF hroot hmin hout

theorem query406 (halph : AlphabetComplete link10 alphabets) : ActualObstruction link10 {3,6,7,9} := rep000 halph

theorem rep001 (halph : AlphabetComplete link10 alphabets) :
    ActualObstruction link10 FastDual10_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link10 rootCodes root_binding alphabets halph nonincident_complete
    FastDual10_001.pointList FastDual10_001.columns FastDual10_001.rows FastDual10_001.bound (by decide +kernel)
    FastDual10_001.column_mask FastDual10_001.checked hc F hF hroot hmin hout

theorem query407 (halph : AlphabetComplete link10 alphabets) : ActualObstruction link10 {3,6,7,10} := rep001 halph

def symmetry408 : Equiv.Perm Point where
  toFun := ![1,0,2,3,5,4,6,7,8,9,11,10,12]
  invFun := ![1,0,2,3,5,4,6,7,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query408 (halph : AlphabetComplete link10 alphabets) : ActualObstruction link10 {3,6,7,11} :=
  obstruction_transport link10 FastDual10_001.points {3,6,7,11} symmetry408
    (by decide +kernel) (root_symmetry_of_codes rootCodes link10 root_binding symmetry408 (by decide +kernel)) (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link10 alphabets) :
    ActualObstruction link10 FastDual10_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link10 rootCodes root_binding alphabets halph nonincident_complete
    FastDual10_002.pointList FastDual10_002.columns FastDual10_002.rows FastDual10_002.bound (by decide +kernel)
    FastDual10_002.column_mask FastDual10_002.checked hc F hF hroot hmin hout

theorem query412 (halph : AlphabetComplete link10 alphabets) : ActualObstruction link10 {3,6,9,10} := rep002 halph

def symmetry413 : Equiv.Perm Point where
  toFun := ![1,0,2,3,5,4,6,7,8,9,11,10,12]
  invFun := ![1,0,2,3,5,4,6,7,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query413 (halph : AlphabetComplete link10 alphabets) : ActualObstruction link10 {3,6,9,11} :=
  obstruction_transport link10 FastDual10_002.points {3,6,9,11} symmetry413
    (by decide +kernel) (root_symmetry_of_codes rootCodes link10 root_binding symmetry413 (by decide +kernel)) (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link10 alphabets) :
    ActualObstruction link10 FastDual10_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link10 rootCodes root_binding alphabets halph nonincident_complete
    FastDual10_003.pointList FastDual10_003.columns FastDual10_003.rows FastDual10_003.bound (by decide +kernel)
    FastDual10_003.column_mask FastDual10_003.checked hc F hF hroot hmin hout

theorem query414 (halph : AlphabetComplete link10 alphabets) : ActualObstruction link10 {3,6,10,11} := rep003 halph

theorem rep004 (halph : AlphabetComplete link10 alphabets) :
    ActualObstruction link10 FastDual10_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link10 rootCodes root_binding alphabets halph nonincident_complete
    FastDual10_004.pointList FastDual10_004.columns FastDual10_004.rows FastDual10_004.bound (by decide +kernel)
    FastDual10_004.column_mask FastDual10_004.checked hc F hF hroot hmin hout

theorem query418 (halph : AlphabetComplete link10 alphabets) : ActualObstruction link10 {3,7,9,10} := rep004 halph

def symmetry419 : Equiv.Perm Point where
  toFun := ![1,0,2,3,5,4,6,7,8,9,11,10,12]
  invFun := ![1,0,2,3,5,4,6,7,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query419 (halph : AlphabetComplete link10 alphabets) : ActualObstruction link10 {3,7,9,11} :=
  obstruction_transport link10 FastDual10_004.points {3,7,9,11} symmetry419
    (by decide +kernel) (root_symmetry_of_codes rootCodes link10 root_binding symmetry419 (by decide +kernel)) (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link10 alphabets) :
    ActualObstruction link10 FastDual10_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link10 rootCodes root_binding alphabets halph nonincident_complete
    FastDual10_005.pointList FastDual10_005.columns FastDual10_005.rows FastDual10_005.bound (by decide +kernel)
    FastDual10_005.column_mask FastDual10_005.checked hc F hF hroot hmin hout

theorem query420 (halph : AlphabetComplete link10 alphabets) : ActualObstruction link10 {3,7,10,11} := rep005 halph

theorem rep006 (halph : AlphabetComplete link10 alphabets) :
    ActualObstruction link10 FastDual10_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link10 rootCodes root_binding alphabets halph nonincident_complete
    FastDual10_006.pointList FastDual10_006.columns FastDual10_006.rows FastDual10_006.bound (by decide +kernel)
    FastDual10_006.column_mask FastDual10_006.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link10 alphabets) : ActualObstruction link10 {6,7,10,11} := rep006 halph

theorem rep007 (halph : AlphabetComplete link10 alphabets) :
    ActualObstruction link10 FastDual10_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link10 rootCodes root_binding alphabets halph nonincident_complete
    FastDual10_007.pointList FastDual10_007.columns FastDual10_007.rows FastDual10_007.bound (by decide +kernel)
    FastDual10_007.column_mask FastDual10_007.checked hc F hF hroot hmin hout

theorem query489 (halph : AlphabetComplete link10 alphabets) : ActualObstruction link10 {6,9,10,11} := rep007 halph

def dualQuads : List (Finset Point) := [{3,6,7,9},{3,6,7,10},{3,6,7,11},{3,6,9,10},{3,6,9,11},{3,6,10,11},{3,7,9,10},{3,7,9,11},{3,7,10,11},{6,7,10,11},{6,9,10,11}]

theorem dual_actual (halph : AlphabetComplete link10 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link10 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact query489 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link10 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link10 Q :=
  class_census link10 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source10
