import C13Global.CatalogIrredundance
import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source19
import C13Global.FastGroups.Source19Part00
namespace C13.Global.Relative.Source19
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source19
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link19 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link19 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link19 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link19 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link19 alphabets) :
    ActualObstruction link19 FastDual19_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link19 rootCodes root_binding alphabets halph nonincident_complete
    FastDual19_000.pointList FastDual19_000.columns FastDual19_000.rows FastDual19_000.bound (by decide +kernel)
    FastDual19_000.column_mask FastDual19_000.checked hc F hF hroot hmin hout

theorem query480 (halph : AlphabetComplete link19 alphabets) : ActualObstruction link19 {6,7,8,9} := rep000 halph

def symmetry485 : Equiv.Perm Point where
  toFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  invFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query485 (halph : AlphabetComplete link19 alphabets) : ActualObstruction link19 {6,7,10,11} :=
  obstruction_transport link19 FastDual19_000.points {6,7,10,11} symmetry485
    (by decide +kernel) (root_symmetry_of_codes rootCodes link19 root_binding symmetry485 (by decide +kernel)) (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link19 alphabets) :
    ActualObstruction link19 FastDual19_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link19 rootCodes root_binding alphabets halph nonincident_complete
    FastDual19_001.pointList FastDual19_001.columns FastDual19_001.rows FastDual19_001.bound (by decide +kernel)
    FastDual19_001.column_mask FastDual19_001.checked hc F hF hroot hmin hout

theorem query494 (halph : AlphabetComplete link19 alphabets) : ActualObstruction link19 {8,9,10,11} := rep001 halph

def dualQuads : List (Finset Point) := [{6,7,8,9},{6,7,10,11},{8,9,10,11}]

theorem dual_actual (halph : AlphabetComplete link19 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link19 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl
  · exact query480 halph
  · exact query485 halph
  · exact query494 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link19 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link19 Q :=
  class_census link19 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source19
