import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source11
import C13Global.FastGroups.Source11Part00
namespace C13.Global.Relative.Source11
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source11
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link11 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link11 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link11 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link11 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link11 alphabets) :
    ActualObstruction link11 FastDual11_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link11 rootCodes root_binding alphabets halph nonincident_complete
    FastDual11_000.pointList FastDual11_000.columns FastDual11_000.rows FastDual11_000.bound (by decide +kernel)
    FastDual11_000.column_mask FastDual11_000.checked hc F hF hroot hmin hout

theorem query405 (halph : AlphabetComplete link11 alphabets) : ActualObstruction link11 {3,6,7,8} := rep000 halph

def symmetry406 : Equiv.Perm Point where
  toFun := ![1,0,2,3,4,5,7,6,9,8,10,11,12]
  invFun := ![1,0,2,3,4,5,7,6,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query406 (halph : AlphabetComplete link11 alphabets) : ActualObstruction link11 {3,6,7,9} :=
  obstruction_transport link11 FastDual11_000.points {3,6,7,9} symmetry406
    (by decide +kernel) (root_symmetry_of_codes rootCodes link11 root_binding symmetry406 (by decide +kernel)) (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link11 alphabets) :
    ActualObstruction link11 FastDual11_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link11 rootCodes root_binding alphabets halph nonincident_complete
    FastDual11_001.pointList FastDual11_001.columns FastDual11_001.rows FastDual11_001.bound (by decide +kernel)
    FastDual11_001.column_mask FastDual11_001.checked hc F hF hroot hmin hout

theorem query408 (halph : AlphabetComplete link11 alphabets) : ActualObstruction link11 {3,6,7,11} := rep001 halph

theorem rep002 (halph : AlphabetComplete link11 alphabets) :
    ActualObstruction link11 FastDual11_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link11 rootCodes root_binding alphabets halph nonincident_complete
    FastDual11_002.pointList FastDual11_002.columns FastDual11_002.rows FastDual11_002.bound (by decide +kernel)
    FastDual11_002.column_mask FastDual11_002.checked hc F hF hroot hmin hout

theorem query409 (halph : AlphabetComplete link11 alphabets) : ActualObstruction link11 {3,6,8,9} := rep002 halph

def symmetry415 : Equiv.Perm Point where
  toFun := ![1,0,2,3,4,5,7,6,9,8,10,11,12]
  invFun := ![1,0,2,3,4,5,7,6,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query415 (halph : AlphabetComplete link11 alphabets) : ActualObstruction link11 {3,7,8,9} :=
  obstruction_transport link11 FastDual11_002.points {3,7,8,9} symmetry415
    (by decide +kernel) (root_symmetry_of_codes rootCodes link11 root_binding symmetry415 (by decide +kernel)) (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link11 alphabets) :
    ActualObstruction link11 FastDual11_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link11 rootCodes root_binding alphabets halph nonincident_complete
    FastDual11_003.pointList FastDual11_003.columns FastDual11_003.rows FastDual11_003.bound (by decide +kernel)
    FastDual11_003.column_mask FastDual11_003.checked hc F hF hroot hmin hout

theorem query411 (halph : AlphabetComplete link11 alphabets) : ActualObstruction link11 {3,6,8,11} := rep003 halph

def symmetry419 : Equiv.Perm Point where
  toFun := ![1,0,2,3,4,5,7,6,9,8,10,11,12]
  invFun := ![1,0,2,3,4,5,7,6,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query419 (halph : AlphabetComplete link11 alphabets) : ActualObstruction link11 {3,7,9,11} :=
  obstruction_transport link11 FastDual11_003.points {3,7,9,11} symmetry419
    (by decide +kernel) (root_symmetry_of_codes rootCodes link11 root_binding symmetry419 (by decide +kernel)) (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link11 alphabets) :
    ActualObstruction link11 FastDual11_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link11 rootCodes root_binding alphabets halph nonincident_complete
    FastDual11_004.pointList FastDual11_004.columns FastDual11_004.rows FastDual11_004.bound (by decide +kernel)
    FastDual11_004.column_mask FastDual11_004.checked hc F hF hroot hmin hout

theorem query413 (halph : AlphabetComplete link11 alphabets) : ActualObstruction link11 {3,6,9,11} := rep004 halph

def symmetry417 : Equiv.Perm Point where
  toFun := ![1,0,2,3,4,5,7,6,9,8,10,11,12]
  invFun := ![1,0,2,3,4,5,7,6,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query417 (halph : AlphabetComplete link11 alphabets) : ActualObstruction link11 {3,7,8,11} :=
  obstruction_transport link11 FastDual11_004.points {3,7,8,11} symmetry417
    (by decide +kernel) (root_symmetry_of_codes rootCodes link11 root_binding symmetry417 (by decide +kernel)) (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link11 alphabets) :
    ActualObstruction link11 FastDual11_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link11 rootCodes root_binding alphabets halph nonincident_complete
    FastDual11_005.pointList FastDual11_005.columns FastDual11_005.rows FastDual11_005.bound (by decide +kernel)
    FastDual11_005.column_mask FastDual11_005.checked hc F hF hroot hmin hout

theorem query480 (halph : AlphabetComplete link11 alphabets) : ActualObstruction link11 {6,7,8,9} := rep005 halph

def dualQuads : List (Finset Point) := [{3,6,7,8},{3,6,7,9},{3,6,7,11},{3,6,8,9},{3,7,8,9},{3,6,8,11},{3,7,9,11},{3,6,9,11},{3,7,8,11},{6,7,8,9}]

theorem dual_actual (halph : AlphabetComplete link11 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link11 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query405 halph
  · exact query406 halph
  · exact query408 halph
  · exact query409 halph
  · exact query415 halph
  · exact query411 halph
  · exact query419 halph
  · exact query413 halph
  · exact query417 halph
  · exact query480 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link11 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link11 Q :=
  class_census link11 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source11
