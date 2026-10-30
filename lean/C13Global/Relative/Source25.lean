import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source25
import C13Global.FastGroups.Source25Part00
namespace C13.Global.Relative.Source25
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source25
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link25 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link25 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link25 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link25 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link25 alphabets) :
    ActualObstruction link25 FastDual25_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link25 rootCodes root_binding alphabets halph nonincident_complete
    FastDual25_000.pointList FastDual25_000.columns FastDual25_000.rows FastDual25_000.bound (by decide +kernel)
    FastDual25_000.column_mask FastDual25_000.checked hc F hF hroot hmin hout

theorem query216 (halph : AlphabetComplete link25 alphabets) : ActualObstruction link25 {1,3,6,9} := rep000 halph

def symmetry221 : Equiv.Perm Point where
  toFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  invFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query221 (halph : AlphabetComplete link25 alphabets) : ActualObstruction link25 {1,3,7,10} :=
  obstruction_transport link25 FastDual25_000.points {1,3,7,10} symmetry221
    (by decide +kernel) (root_symmetry_of_codes rootCodes link25 root_binding symmetry221 (by decide +kernel)) (by decide +kernel) (rep000 halph)

def symmetry267 : Equiv.Perm Point where
  toFun := ![5,6,4,7,11,8,10,9,2,1,3,0,12]
  invFun := ![11,9,8,10,2,0,1,3,5,7,6,4,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query267 (halph : AlphabetComplete link25 alphabets) : ActualObstruction link25 {1,6,7,10} :=
  obstruction_transport link25 FastDual25_000.points {1,6,7,10} symmetry267
    (by decide +kernel) (root_symmetry_of_codes rootCodes link25 root_binding symmetry267 (by decide +kernel)) (by decide +kernel) (rep000 halph)

def symmetry278 : Equiv.Perm Point where
  toFun := ![11,9,8,10,2,0,1,3,5,7,6,4,12]
  invFun := ![5,6,4,7,11,8,10,9,2,1,3,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query278 (halph : AlphabetComplete link25 alphabets) : ActualObstruction link25 {1,7,9,10} :=
  obstruction_transport link25 FastDual25_000.points {1,7,9,10} symmetry278
    (by decide +kernel) (root_symmetry_of_codes rootCodes link25 root_binding symmetry278 (by decide +kernel)) (by decide +kernel) (rep000 halph)

def symmetry406 : Equiv.Perm Point where
  toFun := ![4,7,5,6,8,11,9,10,0,3,1,2,12]
  invFun := ![8,10,11,9,0,2,3,1,4,6,7,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query406 (halph : AlphabetComplete link25 alphabets) : ActualObstruction link25 {3,6,7,9} :=
  obstruction_transport link25 FastDual25_000.points {3,6,7,9} symmetry406
    (by decide +kernel) (root_symmetry_of_codes rootCodes link25 root_binding symmetry406 (by decide +kernel)) (by decide +kernel) (rep000 halph)

def symmetry412 : Equiv.Perm Point where
  toFun := ![8,10,11,9,0,2,3,1,4,6,7,5,12]
  invFun := ![4,7,5,6,8,11,9,10,0,3,1,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query412 (halph : AlphabetComplete link25 alphabets) : ActualObstruction link25 {3,6,9,10} :=
  obstruction_transport link25 FastDual25_000.points {3,6,9,10} symmetry412
    (by decide +kernel) (root_symmetry_of_codes rootCodes link25 root_binding symmetry412 (by decide +kernel)) (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link25 alphabets) :
    ActualObstruction link25 FastDual25_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link25 rootCodes root_binding alphabets halph nonincident_complete
    FastDual25_001.pointList FastDual25_001.columns FastDual25_001.rows FastDual25_001.bound (by decide +kernel)
    FastDual25_001.column_mask FastDual25_001.checked hc F hF hroot hmin hout

theorem query217 (halph : AlphabetComplete link25 alphabets) : ActualObstruction link25 {1,3,6,10} := rep001 halph

def symmetry220 : Equiv.Perm Point where
  toFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  invFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query220 (halph : AlphabetComplete link25 alphabets) : ActualObstruction link25 {1,3,7,9} :=
  obstruction_transport link25 FastDual25_001.points {1,3,7,9} symmetry220
    (by decide +kernel) (root_symmetry_of_codes rootCodes link25 root_binding symmetry220 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry266 : Equiv.Perm Point where
  toFun := ![4,7,5,6,8,11,9,10,0,3,1,2,12]
  invFun := ![8,10,11,9,0,2,3,1,4,6,7,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query266 (halph : AlphabetComplete link25 alphabets) : ActualObstruction link25 {1,6,7,9} :=
  obstruction_transport link25 FastDual25_001.points {1,6,7,9} symmetry266
    (by decide +kernel) (root_symmetry_of_codes rootCodes link25 root_binding symmetry266 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry272 : Equiv.Perm Point where
  toFun := ![11,9,8,10,2,0,1,3,5,7,6,4,12]
  invFun := ![5,6,4,7,11,8,10,9,2,1,3,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query272 (halph : AlphabetComplete link25 alphabets) : ActualObstruction link25 {1,6,9,10} :=
  obstruction_transport link25 FastDual25_001.points {1,6,9,10} symmetry272
    (by decide +kernel) (root_symmetry_of_codes rootCodes link25 root_binding symmetry272 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry407 : Equiv.Perm Point where
  toFun := ![5,6,4,7,11,8,10,9,2,1,3,0,12]
  invFun := ![11,9,8,10,2,0,1,3,5,7,6,4,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query407 (halph : AlphabetComplete link25 alphabets) : ActualObstruction link25 {3,6,7,10} :=
  obstruction_transport link25 FastDual25_001.points {3,6,7,10} symmetry407
    (by decide +kernel) (root_symmetry_of_codes rootCodes link25 root_binding symmetry407 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry418 : Equiv.Perm Point where
  toFun := ![8,10,11,9,0,2,3,1,4,6,7,5,12]
  invFun := ![4,7,5,6,8,11,9,10,0,3,1,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query418 (halph : AlphabetComplete link25 alphabets) : ActualObstruction link25 {3,7,9,10} :=
  obstruction_transport link25 FastDual25_001.points {3,7,9,10} symmetry418
    (by decide +kernel) (root_symmetry_of_codes rootCodes link25 root_binding symmetry418 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def dualQuads : List (Finset Point) := [{1,3,6,9},{1,3,7,10},{1,6,7,10},{1,7,9,10},{3,6,7,9},{3,6,9,10},{1,3,6,10},{1,3,7,9},{1,6,7,9},{1,6,9,10},{3,6,7,10},{3,7,9,10}]

theorem dual_actual (halph : AlphabetComplete link25 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link25 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query216 halph
  · exact query221 halph
  · exact query267 halph
  · exact query278 halph
  · exact query406 halph
  · exact query412 halph
  · exact query217 halph
  · exact query220 halph
  · exact query266 halph
  · exact query272 halph
  · exact query407 halph
  · exact query418 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link25 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link25 Q :=
  class_census link25 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source25
