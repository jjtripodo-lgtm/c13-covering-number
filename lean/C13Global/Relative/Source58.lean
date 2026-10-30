import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source58
import C13Global.FastGroups.Source58Part00
namespace C13.Global.Relative.Source58
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source58
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link58 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link58 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link58 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link58 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link58 alphabets) :
    ActualObstruction link58 FastDual58_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link58 rootCodes root_binding alphabets halph nonincident_complete
    FastDual58_000.pointList FastDual58_000.columns FastDual58_000.rows FastDual58_000.bound (by decide +kernel)
    FastDual58_000.column_mask FastDual58_000.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link58 alphabets) : ActualObstruction link58 {2,3,6,7} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![8,9,11,10,1,0,2,3,5,4,6,7,12]
  invFun := ![5,4,6,7,9,8,10,11,0,1,3,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link58 = link58 :=
  root_symmetry_of_codes rootCodes link58 root_binding automorphism000 (by decide +kernel)

theorem query312 (halph : AlphabetComplete link58 alphabets) : ActualObstruction link58 {2,3,10,11} :=
  obstruction_transport link58 FastDual58_000.points {2,3,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

def automorphism001 : Equiv.Perm Point where
  toFun := ![5,4,7,6,9,8,11,10,0,1,2,3,12]
  invFun := ![8,9,10,11,1,0,3,2,5,4,7,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism001_hole : automorphism001 hole = hole := by decide +kernel

theorem automorphism001_root : transport automorphism001 link58 = link58 :=
  root_symmetry_of_codes rootCodes link58 root_binding automorphism001 (by decide +kernel)

theorem query485 (halph : AlphabetComplete link58 alphabets) : ActualObstruction link58 {6,7,10,11} :=
  obstruction_transport link58 FastDual58_000.points {6,7,10,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link58 alphabets) :
    ActualObstruction link58 FastDual58_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link58 rootCodes root_binding alphabets halph nonincident_complete
    FastDual58_001.pointList FastDual58_001.columns FastDual58_001.rows FastDual58_001.bound (by decide +kernel)
    FastDual58_001.column_mask FastDual58_001.checked hc F hF hroot hmin hout

theorem query301 (halph : AlphabetComplete link58 alphabets) : ActualObstruction link58 {2,3,6,10} := rep001 halph

def automorphism002 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism002_hole : automorphism002 hole = hole := by decide +kernel

theorem automorphism002_root : transport automorphism002 link58 = link58 :=
  root_symmetry_of_codes rootCodes link58 root_binding automorphism002 (by decide +kernel)

theorem query306 (halph : AlphabetComplete link58 alphabets) : ActualObstruction link58 {2,3,7,11} :=
  obstruction_transport link58 FastDual58_001.points {2,3,7,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep001 halph)

theorem query352 (halph : AlphabetComplete link58 alphabets) : ActualObstruction link58 {2,6,7,11} :=
  obstruction_transport link58 FastDual58_001.points {2,6,7,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep001 halph)

theorem query358 (halph : AlphabetComplete link58 alphabets) : ActualObstruction link58 {2,6,10,11} :=
  obstruction_transport link58 FastDual58_001.points {2,6,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

def automorphism003 : Equiv.Perm Point where
  toFun := ![5,4,6,7,9,8,10,11,0,1,3,2,12]
  invFun := ![8,9,11,10,1,0,2,3,5,4,6,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism003_hole : automorphism003 hole = hole := by decide +kernel

theorem automorphism003_root : transport automorphism003 link58 = link58 :=
  root_symmetry_of_codes rootCodes link58 root_binding automorphism003 (by decide +kernel)

theorem query407 (halph : AlphabetComplete link58 alphabets) : ActualObstruction link58 {3,6,7,10} :=
  obstruction_transport link58 FastDual58_001.points {3,6,7,10} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep001 halph)

def automorphism004 : Equiv.Perm Point where
  toFun := ![8,9,10,11,1,0,3,2,5,4,7,6,12]
  invFun := ![5,4,7,6,9,8,11,10,0,1,2,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism004_hole : automorphism004 hole = hole := by decide +kernel

theorem automorphism004_root : transport automorphism004 link58 = link58 :=
  root_symmetry_of_codes rootCodes link58 root_binding automorphism004 (by decide +kernel)

theorem query420 (halph : AlphabetComplete link58 alphabets) : ActualObstruction link58 {3,7,10,11} :=
  obstruction_transport link58 FastDual58_001.points {3,7,10,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link58 alphabets) :
    ActualObstruction link58 FastDual58_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link58 rootCodes root_binding alphabets halph nonincident_complete
    FastDual58_002.pointList FastDual58_002.columns FastDual58_002.rows FastDual58_002.bound (by decide +kernel)
    FastDual58_002.column_mask FastDual58_002.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link58 alphabets) : ActualObstruction link58 {2,3,6,11} := rep002 halph

theorem query305 (halph : AlphabetComplete link58 alphabets) : ActualObstruction link58 {2,3,7,10} :=
  obstruction_transport link58 FastDual58_002.points {2,3,7,10} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep002 halph)

theorem query351 (halph : AlphabetComplete link58 alphabets) : ActualObstruction link58 {2,6,7,10} :=
  obstruction_transport link58 FastDual58_002.points {2,6,7,10} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep002 halph)

theorem query364 (halph : AlphabetComplete link58 alphabets) : ActualObstruction link58 {2,7,10,11} :=
  obstruction_transport link58 FastDual58_002.points {2,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem query408 (halph : AlphabetComplete link58 alphabets) : ActualObstruction link58 {3,6,7,11} :=
  obstruction_transport link58 FastDual58_002.points {3,6,7,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep002 halph)

theorem query414 (halph : AlphabetComplete link58 alphabets) : ActualObstruction link58 {3,6,10,11} :=
  obstruction_transport link58 FastDual58_002.points {3,6,10,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep002 halph)

def dualQuads : List (Finset Point) := [{2,3,6,7},{2,3,10,11},{6,7,10,11},{2,3,6,10},{2,3,7,11},{2,6,7,11},{2,6,10,11},{3,6,7,10},{3,7,10,11},{2,3,6,11},{2,3,7,10},{2,6,7,10},{2,7,10,11},{3,6,7,11},{3,6,10,11}]

theorem dual_actual (halph : AlphabetComplete link58 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link58 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query298 halph
  · exact query312 halph
  · exact query485 halph
  · exact query301 halph
  · exact query306 halph
  · exact query352 halph
  · exact query358 halph
  · exact query407 halph
  · exact query420 halph
  · exact query302 halph
  · exact query305 halph
  · exact query351 halph
  · exact query364 halph
  · exact query408 halph
  · exact query414 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link58 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link58 Q :=
  class_census link58 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source58
