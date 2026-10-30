import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source06
import C13Global.FastGroups.Source06Part00
namespace C13.Global.Relative.Source06
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source06
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link06 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link06 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link06 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link06 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link06 alphabets) :
    ActualObstruction link06 FastDual06_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link06 rootCodes root_binding alphabets halph nonincident_complete
    FastDual06_000.pointList FastDual06_000.columns FastDual06_000.rows FastDual06_000.bound (by decide +kernel)
    FastDual06_000.column_mask FastDual06_000.checked hc F hF hroot hmin hout

theorem query415 (halph : AlphabetComplete link06 alphabets) : ActualObstruction link06 {3,7,8,9} := rep000 halph

theorem rep001 (halph : AlphabetComplete link06 alphabets) :
    ActualObstruction link06 FastDual06_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link06 rootCodes root_binding alphabets halph nonincident_complete
    FastDual06_001.pointList FastDual06_001.columns FastDual06_001.rows FastDual06_001.bound (by decide +kernel)
    FastDual06_001.column_mask FastDual06_001.checked hc F hF hroot hmin hout

theorem query416 (halph : AlphabetComplete link06 alphabets) : ActualObstruction link06 {3,7,8,10} := rep001 halph

def symmetry417 : Equiv.Perm Point where
  toFun := ![5,4,6,7,1,0,2,3,8,9,11,10,12]
  invFun := ![5,4,6,7,1,0,2,3,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query417 (halph : AlphabetComplete link06 alphabets) : ActualObstruction link06 {3,7,8,11} :=
  obstruction_transport link06 FastDual06_001.points {3,7,8,11} symmetry417
    (by decide +kernel) (root_symmetry_of_codes rootCodes link06 root_binding symmetry417 (by decide +kernel)) (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link06 alphabets) :
    ActualObstruction link06 FastDual06_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link06 rootCodes root_binding alphabets halph nonincident_complete
    FastDual06_002.pointList FastDual06_002.columns FastDual06_002.rows FastDual06_002.bound (by decide +kernel)
    FastDual06_002.column_mask FastDual06_002.checked hc F hF hroot hmin hout

theorem query418 (halph : AlphabetComplete link06 alphabets) : ActualObstruction link06 {3,7,9,10} := rep002 halph

def symmetry419 : Equiv.Perm Point where
  toFun := ![5,4,6,7,1,0,2,3,8,9,11,10,12]
  invFun := ![5,4,6,7,1,0,2,3,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query419 (halph : AlphabetComplete link06 alphabets) : ActualObstruction link06 {3,7,9,11} :=
  obstruction_transport link06 FastDual06_002.points {3,7,9,11} symmetry419
    (by decide +kernel) (root_symmetry_of_codes rootCodes link06 root_binding symmetry419 (by decide +kernel)) (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link06 alphabets) :
    ActualObstruction link06 FastDual06_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link06 rootCodes root_binding alphabets halph nonincident_complete
    FastDual06_003.pointList FastDual06_003.columns FastDual06_003.rows FastDual06_003.bound (by decide +kernel)
    FastDual06_003.column_mask FastDual06_003.checked hc F hF hroot hmin hout

theorem query420 (halph : AlphabetComplete link06 alphabets) : ActualObstruction link06 {3,7,10,11} := rep003 halph

theorem rep004 (halph : AlphabetComplete link06 alphabets) :
    ActualObstruction link06 FastDual06_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link06 rootCodes root_binding alphabets halph nonincident_complete
    FastDual06_004.pointList FastDual06_004.columns FastDual06_004.rows FastDual06_004.bound (by decide +kernel)
    FastDual06_004.column_mask FastDual06_004.checked hc F hF hroot hmin hout

theorem query494 (halph : AlphabetComplete link06 alphabets) : ActualObstruction link06 {8,9,10,11} := rep004 halph

def dualQuads : List (Finset Point) := [{3,7,8,9},{3,7,8,10},{3,7,8,11},{3,7,9,10},{3,7,9,11},{3,7,10,11},{8,9,10,11}]

theorem dual_actual (halph : AlphabetComplete link06 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link06 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query415 halph
  · exact query416 halph
  · exact query417 halph
  · exact query418 halph
  · exact query419 halph
  · exact query420 halph
  · exact query494 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link06 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link06 Q :=
  class_census link06 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source06
