import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source66
import C13Global.FastGroups.Source66Part00
namespace C13.Global.Relative.Source66
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source66
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link66 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link66 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link66 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link66 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link66 alphabets) :
    ActualObstruction link66 FastDual66_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link66 rootCodes root_binding alphabets halph nonincident_complete
    FastDual66_000.pointList FastDual66_000.columns FastDual66_000.rows FastDual66_000.bound (by decide +kernel)
    FastDual66_000.column_mask FastDual66_000.checked hc F hF hroot hmin hout

theorem query096 (halph : AlphabetComplete link66 alphabets) : ActualObstruction link66 {0,3,6,9} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![7,4,5,6,1,2,3,0,10,9,8,11,12]
  invFun := ![7,4,5,6,1,2,3,0,10,9,8,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link66 = link66 :=
  root_symmetry_of_codes rootCodes link66 root_binding automorphism000 (by decide +kernel)

theorem query406 (halph : AlphabetComplete link66 alphabets) : ActualObstruction link66 {3,6,7,9} :=
  obstruction_transport link66 FastDual66_000.points {3,6,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

def automorphism001 : Equiv.Perm Point where
  toFun := ![11,8,10,9,2,1,3,0,5,6,4,7,12]
  invFun := ![7,5,4,6,10,8,9,11,1,3,2,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism001_hole : automorphism001 hole = hole := by decide +kernel

theorem automorphism001_root : transport automorphism001 link66 = link66 :=
  root_symmetry_of_codes rootCodes link66 root_binding automorphism001 (by decide +kernel)

theorem query413 (halph : AlphabetComplete link66 alphabets) : ActualObstruction link66 {3,6,9,11} :=
  obstruction_transport link66 FastDual66_000.points {3,6,9,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link66 alphabets) :
    ActualObstruction link66 FastDual66_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link66 rootCodes root_binding alphabets halph nonincident_complete
    FastDual66_001.pointList FastDual66_001.columns FastDual66_001.rows FastDual66_001.bound (by decide +kernel)
    FastDual66_001.column_mask FastDual66_001.checked hc F hF hroot hmin hout

theorem query098 (halph : AlphabetComplete link66 alphabets) : ActualObstruction link66 {0,3,6,11} := rep001 halph

def automorphism002 : Equiv.Perm Point where
  toFun := ![0,2,1,3,8,10,9,11,4,6,5,7,12]
  invFun := ![0,2,1,3,8,10,9,11,4,6,5,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism002_hole : automorphism002 hole = hole := by decide +kernel

theorem automorphism002_root : transport automorphism002 link66 = link66 :=
  root_symmetry_of_codes rootCodes link66 root_binding automorphism002 (by decide +kernel)

theorem query100 (halph : AlphabetComplete link66 alphabets) : ActualObstruction link66 {0,3,7,9} :=
  obstruction_transport link66 FastDual66_001.points {0,3,7,9} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep001 halph)

def automorphism003 : Equiv.Perm Point where
  toFun := ![7,5,4,6,10,8,9,11,1,3,2,0,12]
  invFun := ![11,8,10,9,2,1,3,0,5,6,4,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism003_hole : automorphism003 hole = hole := by decide +kernel

theorem automorphism003_root : transport automorphism003 link66 = link66 :=
  root_symmetry_of_codes rootCodes link66 root_binding automorphism003 (by decide +kernel)

theorem query146 (halph : AlphabetComplete link66 alphabets) : ActualObstruction link66 {0,6,7,9} :=
  obstruction_transport link66 FastDual66_001.points {0,6,7,9} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep001 halph)

def automorphism004 : Equiv.Perm Point where
  toFun := ![11,10,8,9,5,4,6,7,2,3,1,0,12]
  invFun := ![11,10,8,9,5,4,6,7,2,3,1,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism004_hole : automorphism004 hole = hole := by decide +kernel

theorem automorphism004_root : transport automorphism004 link66 = link66 :=
  root_symmetry_of_codes rootCodes link66 root_binding automorphism004 (by decide +kernel)

theorem query153 (halph : AlphabetComplete link66 alphabets) : ActualObstruction link66 {0,6,9,11} :=
  obstruction_transport link66 FastDual66_001.points {0,6,9,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep001 halph)

theorem query408 (halph : AlphabetComplete link66 alphabets) : ActualObstruction link66 {3,6,7,11} :=
  obstruction_transport link66 FastDual66_001.points {3,6,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

theorem query419 (halph : AlphabetComplete link66 alphabets) : ActualObstruction link66 {3,7,9,11} :=
  obstruction_transport link66 FastDual66_001.points {3,7,9,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link66 alphabets) :
    ActualObstruction link66 FastDual66_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link66 rootCodes root_binding alphabets halph nonincident_complete
    FastDual66_002.pointList FastDual66_002.columns FastDual66_002.rows FastDual66_002.bound (by decide +kernel)
    FastDual66_002.column_mask FastDual66_002.checked hc F hF hroot hmin hout

theorem query102 (halph : AlphabetComplete link66 alphabets) : ActualObstruction link66 {0,3,7,11} := rep002 halph

theorem query148 (halph : AlphabetComplete link66 alphabets) : ActualObstruction link66 {0,6,7,11} :=
  obstruction_transport link66 FastDual66_002.points {0,6,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem query159 (halph : AlphabetComplete link66 alphabets) : ActualObstruction link66 {0,7,9,11} :=
  obstruction_transport link66 FastDual66_002.points {0,7,9,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep002 halph)

def dualQuads : List (Finset Point) := [{0,3,6,9},{3,6,7,9},{3,6,9,11},{0,3,6,11},{0,3,7,9},{0,6,7,9},{0,6,9,11},{3,6,7,11},{3,7,9,11},{0,3,7,11},{0,6,7,11},{0,7,9,11}]

theorem dual_actual (halph : AlphabetComplete link66 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link66 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query096 halph
  · exact query406 halph
  · exact query413 halph
  · exact query098 halph
  · exact query100 halph
  · exact query146 halph
  · exact query153 halph
  · exact query408 halph
  · exact query419 halph
  · exact query102 halph
  · exact query148 halph
  · exact query159 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link66 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link66 Q :=
  class_census link66 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source66
