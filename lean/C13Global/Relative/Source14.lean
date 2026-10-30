import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source14
import C13Global.FastGroups.Source14Part00
namespace C13.Global.Relative.Source14
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source14
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link14 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link14 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link14 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link14 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link14 alphabets) :
    ActualObstruction link14 FastDual14_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link14 rootCodes root_binding alphabets halph nonincident_complete
    FastDual14_000.pointList FastDual14_000.columns FastDual14_000.rows FastDual14_000.bound (by decide +kernel)
    FastDual14_000.column_mask FastDual14_000.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link14 alphabets) : ActualObstruction link14 {2,3,6,7} := rep000 halph

def symmetry307 : Equiv.Perm Point where
  toFun := ![11,10,9,8,1,0,3,2,6,7,4,5,12]
  invFun := ![5,4,7,6,10,11,8,9,3,2,1,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query307 (halph : AlphabetComplete link14 alphabets) : ActualObstruction link14 {2,3,8,9} :=
  obstruction_transport link14 FastDual14_000.points {2,3,8,9} symmetry307
    (by decide +kernel) (root_symmetry_of_codes rootCodes link14 root_binding symmetry307 (by decide +kernel)) (by decide +kernel) (rep000 halph)

def symmetry480 : Equiv.Perm Point where
  toFun := ![5,4,7,6,11,10,9,8,2,3,0,1,12]
  invFun := ![10,11,8,9,1,0,3,2,7,6,5,4,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query480 (halph : AlphabetComplete link14 alphabets) : ActualObstruction link14 {6,7,8,9} :=
  obstruction_transport link14 FastDual14_000.points {6,7,8,9} symmetry480
    (by decide +kernel) (root_symmetry_of_codes rootCodes link14 root_binding symmetry480 (by decide +kernel)) (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link14 alphabets) :
    ActualObstruction link14 FastDual14_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link14 rootCodes root_binding alphabets halph nonincident_complete
    FastDual14_001.pointList FastDual14_001.columns FastDual14_001.rows FastDual14_001.bound (by decide +kernel)
    FastDual14_001.column_mask FastDual14_001.checked hc F hF hroot hmin hout

theorem query299 (halph : AlphabetComplete link14 alphabets) : ActualObstruction link14 {2,3,6,8} := rep001 halph

def symmetry300 : Equiv.Perm Point where
  toFun := ![1,0,3,2,4,5,6,7,9,8,11,10,12]
  invFun := ![1,0,3,2,4,5,6,7,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query300 (halph : AlphabetComplete link14 alphabets) : ActualObstruction link14 {2,3,6,9} :=
  obstruction_transport link14 FastDual14_001.points {2,3,6,9} symmetry300
    (by decide +kernel) (root_symmetry_of_codes rootCodes link14 root_binding symmetry300 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry303 : Equiv.Perm Point where
  toFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  invFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query303 (halph : AlphabetComplete link14 alphabets) : ActualObstruction link14 {2,3,7,8} :=
  obstruction_transport link14 FastDual14_001.points {2,3,7,8} symmetry303
    (by decide +kernel) (root_symmetry_of_codes rootCodes link14 root_binding symmetry303 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry304 : Equiv.Perm Point where
  toFun := ![1,0,2,3,4,5,7,6,9,8,10,11,12]
  invFun := ![1,0,2,3,4,5,7,6,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query304 (halph : AlphabetComplete link14 alphabets) : ActualObstruction link14 {2,3,7,9} :=
  obstruction_transport link14 FastDual14_001.points {2,3,7,9} symmetry304
    (by decide +kernel) (root_symmetry_of_codes rootCodes link14 root_binding symmetry304 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry349 : Equiv.Perm Point where
  toFun := ![5,4,6,7,11,10,8,9,2,3,1,0,12]
  invFun := ![11,10,8,9,1,0,2,3,6,7,5,4,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query349 (halph : AlphabetComplete link14 alphabets) : ActualObstruction link14 {2,6,7,8} :=
  obstruction_transport link14 FastDual14_001.points {2,6,7,8} symmetry349
    (by decide +kernel) (root_symmetry_of_codes rootCodes link14 root_binding symmetry349 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry350 : Equiv.Perm Point where
  toFun := ![5,4,7,6,11,10,9,8,2,3,0,1,12]
  invFun := ![10,11,8,9,1,0,3,2,7,6,5,4,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query350 (halph : AlphabetComplete link14 alphabets) : ActualObstruction link14 {2,6,7,9} :=
  obstruction_transport link14 FastDual14_001.points {2,6,7,9} symmetry350
    (by decide +kernel) (root_symmetry_of_codes rootCodes link14 root_binding symmetry350 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry353 : Equiv.Perm Point where
  toFun := ![11,10,8,9,1,0,2,3,6,7,5,4,12]
  invFun := ![5,4,6,7,11,10,8,9,2,3,1,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query353 (halph : AlphabetComplete link14 alphabets) : ActualObstruction link14 {2,6,8,9} :=
  obstruction_transport link14 FastDual14_001.points {2,6,8,9} symmetry353
    (by decide +kernel) (root_symmetry_of_codes rootCodes link14 root_binding symmetry353 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry359 : Equiv.Perm Point where
  toFun := ![11,10,9,8,0,1,2,3,7,6,5,4,12]
  invFun := ![4,5,6,7,11,10,9,8,3,2,1,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query359 (halph : AlphabetComplete link14 alphabets) : ActualObstruction link14 {2,7,8,9} :=
  obstruction_transport link14 FastDual14_001.points {2,7,8,9} symmetry359
    (by decide +kernel) (root_symmetry_of_codes rootCodes link14 root_binding symmetry359 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry405 : Equiv.Perm Point where
  toFun := ![5,4,7,6,10,11,8,9,3,2,1,0,12]
  invFun := ![11,10,9,8,1,0,3,2,6,7,4,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query405 (halph : AlphabetComplete link14 alphabets) : ActualObstruction link14 {3,6,7,8} :=
  obstruction_transport link14 FastDual14_001.points {3,6,7,8} symmetry405
    (by decide +kernel) (root_symmetry_of_codes rootCodes link14 root_binding symmetry405 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry406 : Equiv.Perm Point where
  toFun := ![5,4,6,7,10,11,9,8,3,2,0,1,12]
  invFun := ![10,11,9,8,1,0,2,3,7,6,4,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query406 (halph : AlphabetComplete link14 alphabets) : ActualObstruction link14 {3,6,7,9} :=
  obstruction_transport link14 FastDual14_001.points {3,6,7,9} symmetry406
    (by decide +kernel) (root_symmetry_of_codes rootCodes link14 root_binding symmetry406 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry409 : Equiv.Perm Point where
  toFun := ![11,10,9,8,1,0,3,2,6,7,4,5,12]
  invFun := ![5,4,7,6,10,11,8,9,3,2,1,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query409 (halph : AlphabetComplete link14 alphabets) : ActualObstruction link14 {3,6,8,9} :=
  obstruction_transport link14 FastDual14_001.points {3,6,8,9} symmetry409
    (by decide +kernel) (root_symmetry_of_codes rootCodes link14 root_binding symmetry409 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry415 : Equiv.Perm Point where
  toFun := ![11,10,8,9,0,1,3,2,7,6,4,5,12]
  invFun := ![4,5,7,6,10,11,9,8,2,3,1,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query415 (halph : AlphabetComplete link14 alphabets) : ActualObstruction link14 {3,7,8,9} :=
  obstruction_transport link14 FastDual14_001.points {3,7,8,9} symmetry415
    (by decide +kernel) (root_symmetry_of_codes rootCodes link14 root_binding symmetry415 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def dualQuads : List (Finset Point) := [{2,3,6,7},{2,3,8,9},{6,7,8,9},{2,3,6,8},{2,3,6,9},{2,3,7,8},{2,3,7,9},{2,6,7,8},{2,6,7,9},{2,6,8,9},{2,7,8,9},{3,6,7,8},{3,6,7,9},{3,6,8,9},{3,7,8,9}]

theorem dual_actual (halph : AlphabetComplete link14 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link14 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query298 halph
  · exact query307 halph
  · exact query480 halph
  · exact query299 halph
  · exact query300 halph
  · exact query303 halph
  · exact query304 halph
  · exact query349 halph
  · exact query350 halph
  · exact query353 halph
  · exact query359 halph
  · exact query405 halph
  · exact query406 halph
  · exact query409 halph
  · exact query415 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link14 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link14 Q :=
  class_census link14 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source14
