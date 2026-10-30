import C13Global.LowerBoundCore
import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source13
import C13Global.FastGroups.Source13Part00
namespace C13.Global.Relative.Source13
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source13
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link13 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link13 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link13 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link13 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link13 alphabets) :
    ActualObstruction link13 FastDual13_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link13 rootCodes root_binding alphabets halph nonincident_complete
    FastDual13_000.pointList FastDual13_000.columns FastDual13_000.rows FastDual13_000.bound (by decide +kernel)
    FastDual13_000.column_mask FastDual13_000.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link13 alphabets) : ActualObstruction link13 {2,3,6,7} := rep000 halph

theorem rep001 (halph : AlphabetComplete link13 alphabets) :
    ActualObstruction link13 FastDual13_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link13 rootCodes root_binding alphabets halph nonincident_complete
    FastDual13_001.pointList FastDual13_001.columns FastDual13_001.rows FastDual13_001.bound (by decide +kernel)
    FastDual13_001.column_mask FastDual13_001.checked hc F hF hroot hmin hout

theorem query300 (halph : AlphabetComplete link13 alphabets) : ActualObstruction link13 {2,3,6,9} := rep001 halph

def symmetry304 : Equiv.Perm Point where
  toFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  invFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query304 (halph : AlphabetComplete link13 alphabets) : ActualObstruction link13 {2,3,7,9} :=
  obstruction_transport link13 FastDual13_001.points {2,3,7,9} symmetry304
    (by decide +kernel) (root_symmetry_of_codes rootCodes link13 root_binding symmetry304 (by decide +kernel)) (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link13 alphabets) :
    ActualObstruction link13 FastDual13_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link13 rootCodes root_binding alphabets halph nonincident_complete
    FastDual13_002.pointList FastDual13_002.columns FastDual13_002.rows FastDual13_002.bound (by decide +kernel)
    FastDual13_002.column_mask FastDual13_002.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link13 alphabets) : ActualObstruction link13 {2,3,6,11} := rep002 halph

def symmetry306 : Equiv.Perm Point where
  toFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  invFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query306 (halph : AlphabetComplete link13 alphabets) : ActualObstruction link13 {2,3,7,11} :=
  obstruction_transport link13 FastDual13_002.points {2,3,7,11} symmetry306
    (by decide +kernel) (root_symmetry_of_codes rootCodes link13 root_binding symmetry306 (by decide +kernel)) (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link13 alphabets) :
    ActualObstruction link13 FastDual13_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link13 rootCodes root_binding alphabets halph nonincident_complete
    FastDual13_003.pointList FastDual13_003.columns FastDual13_003.rows FastDual13_003.bound (by decide +kernel)
    FastDual13_003.column_mask FastDual13_003.checked hc F hF hroot hmin hout

theorem query350 (halph : AlphabetComplete link13 alphabets) : ActualObstruction link13 {2,6,7,9} := rep003 halph

def symmetry406 : Equiv.Perm Point where
  toFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  invFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query406 (halph : AlphabetComplete link13 alphabets) : ActualObstruction link13 {3,6,7,9} :=
  obstruction_transport link13 FastDual13_003.points {3,6,7,9} symmetry406
    (by decide +kernel) (root_symmetry_of_codes rootCodes link13 root_binding symmetry406 (by decide +kernel)) (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link13 alphabets) :
    ActualObstruction link13 FastDual13_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link13 rootCodes root_binding alphabets halph nonincident_complete
    FastDual13_004.pointList FastDual13_004.columns FastDual13_004.rows FastDual13_004.bound (by decide +kernel)
    FastDual13_004.column_mask FastDual13_004.checked hc F hF hroot hmin hout

theorem query352 (halph : AlphabetComplete link13 alphabets) : ActualObstruction link13 {2,6,7,11} := rep004 halph

def symmetry408 : Equiv.Perm Point where
  toFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  invFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query408 (halph : AlphabetComplete link13 alphabets) : ActualObstruction link13 {3,6,7,11} :=
  obstruction_transport link13 FastDual13_004.points {3,6,7,11} symmetry408
    (by decide +kernel) (root_symmetry_of_codes rootCodes link13 root_binding symmetry408 (by decide +kernel)) (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link13 alphabets) :
    ActualObstruction link13 FastDual13_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link13 rootCodes root_binding alphabets halph nonincident_complete
    FastDual13_005.pointList FastDual13_005.columns FastDual13_005.rows FastDual13_005.bound (by decide +kernel)
    FastDual13_005.column_mask FastDual13_005.checked hc F hF hroot hmin hout

theorem query357 (halph : AlphabetComplete link13 alphabets) : ActualObstruction link13 {2,6,9,11} := rep005 halph

def symmetry419 : Equiv.Perm Point where
  toFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  invFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query419 (halph : AlphabetComplete link13 alphabets) : ActualObstruction link13 {3,7,9,11} :=
  obstruction_transport link13 FastDual13_005.points {3,7,9,11} symmetry419
    (by decide +kernel) (root_symmetry_of_codes rootCodes link13 root_binding symmetry419 (by decide +kernel)) (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link13 alphabets) :
    ActualObstruction link13 FastDual13_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link13 rootCodes root_binding alphabets halph nonincident_complete
    FastDual13_006.pointList FastDual13_006.columns FastDual13_006.rows FastDual13_006.bound (by decide +kernel)
    FastDual13_006.column_mask FastDual13_006.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link13 alphabets) : ActualObstruction link13 {2,7,9,11} := rep006 halph

def symmetry413 : Equiv.Perm Point where
  toFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  invFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query413 (halph : AlphabetComplete link13 alphabets) : ActualObstruction link13 {3,6,9,11} :=
  obstruction_transport link13 FastDual13_006.points {3,6,9,11} symmetry413
    (by decide +kernel) (root_symmetry_of_codes rootCodes link13 root_binding symmetry413 (by decide +kernel)) (by decide +kernel) (rep006 halph)

def dualQuads : List (Finset Point) := [{2,3,6,7},{2,3,6,9},{2,3,7,9},{2,3,6,11},{2,3,7,11},{2,6,7,9},{3,6,7,9},{2,6,7,11},{3,6,7,11},{2,6,9,11},{3,7,9,11},{2,7,9,11},{3,6,9,11}]

theorem dual_actual (halph : AlphabetComplete link13 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link13 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query298 halph
  · exact query300 halph
  · exact query304 halph
  · exact query302 halph
  · exact query306 halph
  · exact query350 halph
  · exact query406 halph
  · exact query352 halph
  · exact query408 halph
  · exact query357 halph
  · exact query419 halph
  · exact query363 halph
  · exact query413 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link13 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link13 Q :=
  class_census link13 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source13
