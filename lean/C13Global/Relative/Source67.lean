import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source67
import C13Global.FastGroups.Source67Part00
namespace C13.Global.Relative.Source67
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source67
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link67 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link67 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link67 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link67 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link67 alphabets) :
    ActualObstruction link67 FastDual67_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link67 rootCodes root_binding alphabets halph nonincident_complete
    FastDual67_000.pointList FastDual67_000.columns FastDual67_000.rows FastDual67_000.bound (by decide +kernel)
    FastDual67_000.column_mask FastDual67_000.checked hc F hF hroot hmin hout

theorem query061 (halph : AlphabetComplete link67 alphabets) : ActualObstruction link67 {0,2,5,7} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![0,3,2,1,8,11,10,9,4,7,6,5,12]
  invFun := ![0,3,2,1,8,11,10,9,4,7,6,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link67 = link67 :=
  root_symmetry_of_codes rootCodes link67 root_binding automorphism000 (by decide +kernel)

theorem query079 (halph : AlphabetComplete link67 alphabets) : ActualObstruction link67 {0,2,9,11} :=
  obstruction_transport link67 FastDual67_000.points {0,2,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

def automorphism001 : Equiv.Perm Point where
  toFun := ![7,6,5,4,10,11,8,9,1,0,3,2,12]
  invFun := ![9,8,11,10,3,2,1,0,6,7,4,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism001_hole : automorphism001 hole = hole := by decide +kernel

theorem automorphism001_root : transport automorphism001 link67 = link67 :=
  root_symmetry_of_codes rootCodes link67 root_binding automorphism001 (by decide +kernel)

theorem query474 (halph : AlphabetComplete link67 alphabets) : ActualObstruction link67 {5,7,9,11} :=
  obstruction_transport link67 FastDual67_000.points {5,7,9,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link67 alphabets) :
    ActualObstruction link67 FastDual67_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link67 rootCodes root_binding alphabets halph nonincident_complete
    FastDual67_001.pointList FastDual67_001.columns FastDual67_001.rows FastDual67_001.bound (by decide +kernel)
    FastDual67_001.column_mask FastDual67_001.checked hc F hF hroot hmin hout

theorem query063 (halph : AlphabetComplete link67 alphabets) : ActualObstruction link67 {0,2,5,9} := rep001 halph

theorem query074 (halph : AlphabetComplete link67 alphabets) : ActualObstruction link67 {0,2,7,11} :=
  obstruction_transport link67 FastDual67_001.points {0,2,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

theorem query138 (halph : AlphabetComplete link67 alphabets) : ActualObstruction link67 {0,5,7,11} :=
  obstruction_transport link67 FastDual67_001.points {0,5,7,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep001 halph)

def automorphism002 : Equiv.Perm Point where
  toFun := ![9,10,11,8,6,5,4,7,3,0,1,2,12]
  invFun := ![9,10,11,8,6,5,4,7,3,0,1,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism002_hole : automorphism002 hole = hole := by decide +kernel

theorem automorphism002_root : transport automorphism002 link67 = link67 :=
  root_symmetry_of_codes rootCodes link67 root_binding automorphism002 (by decide +kernel)

theorem query143 (halph : AlphabetComplete link67 alphabets) : ActualObstruction link67 {0,5,9,11} :=
  obstruction_transport link67 FastDual67_001.points {0,5,9,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep001 halph)

def automorphism003 : Equiv.Perm Point where
  toFun := ![7,4,5,6,1,2,3,0,10,9,8,11,12]
  invFun := ![7,4,5,6,1,2,3,0,10,9,8,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism003_hole : automorphism003 hole = hole := by decide +kernel

theorem automorphism003_root : transport automorphism003 link67 = link67 :=
  root_symmetry_of_codes rootCodes link67 root_binding automorphism003 (by decide +kernel)

theorem query340 (halph : AlphabetComplete link67 alphabets) : ActualObstruction link67 {2,5,7,9} :=
  obstruction_transport link67 FastDual67_001.points {2,5,7,9} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep001 halph)

def automorphism004 : Equiv.Perm Point where
  toFun := ![9,8,11,10,3,2,1,0,6,7,4,5,12]
  invFun := ![7,6,5,4,10,11,8,9,1,0,3,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism004_hole : automorphism004 hole = hole := by decide +kernel

theorem automorphism004_root : transport automorphism004 link67 = link67 :=
  root_symmetry_of_codes rootCodes link67 root_binding automorphism004 (by decide +kernel)

theorem query363 (halph : AlphabetComplete link67 alphabets) : ActualObstruction link67 {2,7,9,11} :=
  obstruction_transport link67 FastDual67_001.points {2,7,9,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link67 alphabets) :
    ActualObstruction link67 FastDual67_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link67 rootCodes root_binding alphabets halph nonincident_complete
    FastDual67_002.pointList FastDual67_002.columns FastDual67_002.rows FastDual67_002.bound (by decide +kernel)
    FastDual67_002.column_mask FastDual67_002.checked hc F hF hroot hmin hout

theorem query065 (halph : AlphabetComplete link67 alphabets) : ActualObstruction link67 {0,2,5,11} := rep002 halph

theorem query342 (halph : AlphabetComplete link67 alphabets) : ActualObstruction link67 {2,5,7,11} :=
  obstruction_transport link67 FastDual67_002.points {2,5,7,11} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep002 halph)

theorem query347 (halph : AlphabetComplete link67 alphabets) : ActualObstruction link67 {2,5,9,11} :=
  obstruction_transport link67 FastDual67_002.points {2,5,9,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link67 alphabets) :
    ActualObstruction link67 FastDual67_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link67 rootCodes root_binding alphabets halph nonincident_complete
    FastDual67_003.pointList FastDual67_003.columns FastDual67_003.rows FastDual67_003.bound (by decide +kernel)
    FastDual67_003.column_mask FastDual67_003.checked hc F hF hroot hmin hout

theorem query072 (halph : AlphabetComplete link67 alphabets) : ActualObstruction link67 {0,2,7,9} := rep003 halph

theorem query136 (halph : AlphabetComplete link67 alphabets) : ActualObstruction link67 {0,5,7,9} :=
  obstruction_transport link67 FastDual67_003.points {0,5,7,9} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep003 halph)

theorem query159 (halph : AlphabetComplete link67 alphabets) : ActualObstruction link67 {0,7,9,11} :=
  obstruction_transport link67 FastDual67_003.points {0,7,9,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep003 halph)

def dualQuads : List (Finset Point) := [{0,2,5,7},{0,2,9,11},{5,7,9,11},{0,2,5,9},{0,2,7,11},{0,5,7,11},{0,5,9,11},{2,5,7,9},{2,7,9,11},{0,2,5,11},{2,5,7,11},{2,5,9,11},{0,2,7,9},{0,5,7,9},{0,7,9,11}]

theorem dual_actual (halph : AlphabetComplete link67 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link67 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query061 halph
  · exact query079 halph
  · exact query474 halph
  · exact query063 halph
  · exact query074 halph
  · exact query138 halph
  · exact query143 halph
  · exact query340 halph
  · exact query363 halph
  · exact query065 halph
  · exact query342 halph
  · exact query347 halph
  · exact query072 halph
  · exact query136 halph
  · exact query159 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link67 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link67 Q :=
  class_census link67 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source67
