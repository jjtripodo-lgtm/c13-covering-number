import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source39
import C13Global.FastGroups.Source39Part00
namespace C13.Global.Relative.Source39
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source39
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link39 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link39 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link39 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link39 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link39 alphabets) :
    ActualObstruction link39 FastDual39_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link39 rootCodes root_binding alphabets halph nonincident_complete
    FastDual39_000.pointList FastDual39_000.columns FastDual39_000.rows FastDual39_000.bound (by decide +kernel)
    FastDual39_000.column_mask FastDual39_000.checked hc F hF hroot hmin hout

theorem query198 (halph : AlphabetComplete link39 alphabets) : ActualObstruction link39 {1,2,9,10} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link39 = link39 :=
  root_symmetry_of_codes rootCodes link39 root_binding automorphism000 (by decide +kernel)

theorem query227 (halph : AlphabetComplete link39 alphabets) : ActualObstruction link39 {1,3,9,11} :=
  obstruction_transport link39 FastDual39_000.points {1,3,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link39 alphabets) :
    ActualObstruction link39 FastDual39_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link39 rootCodes root_binding alphabets halph nonincident_complete
    FastDual39_001.pointList FastDual39_001.columns FastDual39_001.rows FastDual39_001.bound (by decide +kernel)
    FastDual39_001.column_mask FastDual39_001.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link39 alphabets) : ActualObstruction link39 {2,3,10,11} := rep001 halph

def dualQuads : List (Finset Point) := [{1,2,9,10},{1,3,9,11},{2,3,10,11}]

theorem dual_actual (halph : AlphabetComplete link39 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link39 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl
  · exact query198 halph
  · exact query227 halph
  · exact query312 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link39 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link39 Q :=
  class_census link39 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source39
