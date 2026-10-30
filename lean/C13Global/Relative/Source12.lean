import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source12
import C13Global.FastGroups.Source12Part00
namespace C13.Global.Relative.Source12
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source12
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link12 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link12 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link12 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link12 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link12 alphabets) :
    ActualObstruction link12 FastDual12_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link12 rootCodes root_binding alphabets halph nonincident_complete
    FastDual12_000.pointList FastDual12_000.columns FastDual12_000.rows FastDual12_000.bound (by decide +kernel)
    FastDual12_000.column_mask FastDual12_000.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link12 alphabets) : ActualObstruction link12 {2,3,6,7} := rep000 halph

def symmetry312 : Equiv.Perm Point where
  toFun := ![8,9,11,10,0,1,3,2,4,5,7,6,12]
  invFun := ![4,5,7,6,8,9,11,10,0,1,3,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query312 (halph : AlphabetComplete link12 alphabets) : ActualObstruction link12 {2,3,10,11} :=
  obstruction_transport link12 FastDual12_000.points {2,3,10,11} symmetry312
    (by decide +kernel) (root_symmetry_of_codes rootCodes link12 root_binding symmetry312 (by decide +kernel)) (by decide +kernel) (rep000 halph)

def symmetry485 : Equiv.Perm Point where
  toFun := ![4,5,7,6,8,9,11,10,0,1,3,2,12]
  invFun := ![8,9,11,10,0,1,3,2,4,5,7,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query485 (halph : AlphabetComplete link12 alphabets) : ActualObstruction link12 {6,7,10,11} :=
  obstruction_transport link12 FastDual12_000.points {6,7,10,11} symmetry485
    (by decide +kernel) (root_symmetry_of_codes rootCodes link12 root_binding symmetry485 (by decide +kernel)) (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link12 alphabets) :
    ActualObstruction link12 FastDual12_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link12 rootCodes root_binding alphabets halph nonincident_complete
    FastDual12_001.pointList FastDual12_001.columns FastDual12_001.rows FastDual12_001.bound (by decide +kernel)
    FastDual12_001.column_mask FastDual12_001.checked hc F hF hroot hmin hout

theorem query301 (halph : AlphabetComplete link12 alphabets) : ActualObstruction link12 {2,3,6,10} := rep001 halph

def symmetry302 : Equiv.Perm Point where
  toFun := ![1,0,3,2,4,5,6,7,9,8,11,10,12]
  invFun := ![1,0,3,2,4,5,6,7,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query302 (halph : AlphabetComplete link12 alphabets) : ActualObstruction link12 {2,3,6,11} :=
  obstruction_transport link12 FastDual12_001.points {2,3,6,11} symmetry302
    (by decide +kernel) (root_symmetry_of_codes rootCodes link12 root_binding symmetry302 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry305 : Equiv.Perm Point where
  toFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  invFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query305 (halph : AlphabetComplete link12 alphabets) : ActualObstruction link12 {2,3,7,10} :=
  obstruction_transport link12 FastDual12_001.points {2,3,7,10} symmetry305
    (by decide +kernel) (root_symmetry_of_codes rootCodes link12 root_binding symmetry305 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry306 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query306 (halph : AlphabetComplete link12 alphabets) : ActualObstruction link12 {2,3,7,11} :=
  obstruction_transport link12 FastDual12_001.points {2,3,7,11} symmetry306
    (by decide +kernel) (root_symmetry_of_codes rootCodes link12 root_binding symmetry306 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry351 : Equiv.Perm Point where
  toFun := ![4,5,7,6,9,8,10,11,1,0,2,3,12]
  invFun := ![9,8,10,11,0,1,3,2,5,4,6,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query351 (halph : AlphabetComplete link12 alphabets) : ActualObstruction link12 {2,6,7,10} :=
  obstruction_transport link12 FastDual12_001.points {2,6,7,10} symmetry351
    (by decide +kernel) (root_symmetry_of_codes rootCodes link12 root_binding symmetry351 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry352 : Equiv.Perm Point where
  toFun := ![5,4,7,6,9,8,11,10,0,1,2,3,12]
  invFun := ![8,9,10,11,1,0,3,2,5,4,7,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query352 (halph : AlphabetComplete link12 alphabets) : ActualObstruction link12 {2,6,7,11} :=
  obstruction_transport link12 FastDual12_001.points {2,6,7,11} symmetry352
    (by decide +kernel) (root_symmetry_of_codes rootCodes link12 root_binding symmetry352 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry358 : Equiv.Perm Point where
  toFun := ![8,9,11,10,1,0,2,3,5,4,6,7,12]
  invFun := ![5,4,6,7,9,8,10,11,0,1,3,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query358 (halph : AlphabetComplete link12 alphabets) : ActualObstruction link12 {2,6,10,11} :=
  obstruction_transport link12 FastDual12_001.points {2,6,10,11} symmetry358
    (by decide +kernel) (root_symmetry_of_codes rootCodes link12 root_binding symmetry358 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry364 : Equiv.Perm Point where
  toFun := ![9,8,11,10,0,1,2,3,5,4,7,6,12]
  invFun := ![4,5,6,7,9,8,11,10,1,0,3,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query364 (halph : AlphabetComplete link12 alphabets) : ActualObstruction link12 {2,7,10,11} :=
  obstruction_transport link12 FastDual12_001.points {2,7,10,11} symmetry364
    (by decide +kernel) (root_symmetry_of_codes rootCodes link12 root_binding symmetry364 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry407 : Equiv.Perm Point where
  toFun := ![5,4,7,6,8,9,10,11,1,0,3,2,12]
  invFun := ![9,8,11,10,1,0,3,2,4,5,6,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query407 (halph : AlphabetComplete link12 alphabets) : ActualObstruction link12 {3,6,7,10} :=
  obstruction_transport link12 FastDual12_001.points {3,6,7,10} symmetry407
    (by decide +kernel) (root_symmetry_of_codes rootCodes link12 root_binding symmetry407 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry408 : Equiv.Perm Point where
  toFun := ![4,5,7,6,8,9,11,10,0,1,3,2,12]
  invFun := ![8,9,11,10,0,1,3,2,4,5,7,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query408 (halph : AlphabetComplete link12 alphabets) : ActualObstruction link12 {3,6,7,11} :=
  obstruction_transport link12 FastDual12_001.points {3,6,7,11} symmetry408
    (by decide +kernel) (root_symmetry_of_codes rootCodes link12 root_binding symmetry408 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry414 : Equiv.Perm Point where
  toFun := ![9,8,11,10,1,0,3,2,4,5,6,7,12]
  invFun := ![5,4,7,6,8,9,10,11,1,0,3,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query414 (halph : AlphabetComplete link12 alphabets) : ActualObstruction link12 {3,6,10,11} :=
  obstruction_transport link12 FastDual12_001.points {3,6,10,11} symmetry414
    (by decide +kernel) (root_symmetry_of_codes rootCodes link12 root_binding symmetry414 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry420 : Equiv.Perm Point where
  toFun := ![8,9,11,10,0,1,3,2,4,5,7,6,12]
  invFun := ![4,5,7,6,8,9,11,10,0,1,3,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query420 (halph : AlphabetComplete link12 alphabets) : ActualObstruction link12 {3,7,10,11} :=
  obstruction_transport link12 FastDual12_001.points {3,7,10,11} symmetry420
    (by decide +kernel) (root_symmetry_of_codes rootCodes link12 root_binding symmetry420 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def dualQuads : List (Finset Point) := [{2,3,6,7},{2,3,10,11},{6,7,10,11},{2,3,6,10},{2,3,6,11},{2,3,7,10},{2,3,7,11},{2,6,7,10},{2,6,7,11},{2,6,10,11},{2,7,10,11},{3,6,7,10},{3,6,7,11},{3,6,10,11},{3,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link12 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link12 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query298 halph
  · exact query312 halph
  · exact query485 halph
  · exact query301 halph
  · exact query302 halph
  · exact query305 halph
  · exact query306 halph
  · exact query351 halph
  · exact query352 halph
  · exact query358 halph
  · exact query364 halph
  · exact query407 halph
  · exact query408 halph
  · exact query414 halph
  · exact query420 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link12 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link12 Q :=
  class_census link12 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source12
