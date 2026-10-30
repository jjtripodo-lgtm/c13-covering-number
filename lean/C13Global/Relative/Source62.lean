import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source62
import C13Global.FastGroups.Source62Part00
namespace C13.Global.Relative.Source62
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source62
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link62 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link62 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link62 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link62 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link62 alphabets) :
    ActualObstruction link62 FastDual62_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link62 rootCodes root_binding alphabets halph nonincident_complete
    FastDual62_000.pointList FastDual62_000.columns FastDual62_000.rows FastDual62_000.bound (by decide +kernel)
    FastDual62_000.column_mask FastDual62_000.checked hc F hF hroot hmin hout

theorem query212 (halph : AlphabetComplete link62 alphabets) : ActualObstruction link62 {1,3,5,10} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![9,11,8,10,7,5,6,4,2,0,3,1,12]
  invFun := ![9,11,8,10,7,5,6,4,2,0,3,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link62 = link62 :=
  root_symmetry_of_codes rootCodes link62 root_binding automorphism000 (by decide +kernel)

theorem query404 (halph : AlphabetComplete link62 alphabets) : ActualObstruction link62 {3,5,10,11} :=
  obstruction_transport link62 FastDual62_000.points {3,5,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link62 alphabets) :
    ActualObstruction link62 FastDual62_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link62 rootCodes root_binding alphabets halph nonincident_complete
    FastDual62_001.pointList FastDual62_001.columns FastDual62_001.rows FastDual62_001.bound (by decide +kernel)
    FastDual62_001.column_mask FastDual62_001.checked hc F hF hroot hmin hout

theorem query213 (halph : AlphabetComplete link62 alphabets) : ActualObstruction link62 {1,3,5,11} := rep001 halph

theorem query264 (halph : AlphabetComplete link62 alphabets) : ActualObstruction link62 {1,5,10,11} :=
  obstruction_transport link62 FastDual62_001.points {1,5,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link62 alphabets) :
    ActualObstruction link62 FastDual62_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link62 rootCodes root_binding alphabets halph nonincident_complete
    FastDual62_002.pointList FastDual62_002.columns FastDual62_002.rows FastDual62_002.bound (by decide +kernel)
    FastDual62_002.column_mask FastDual62_002.checked hc F hF hroot hmin hout

theorem query217 (halph : AlphabetComplete link62 alphabets) : ActualObstruction link62 {1,3,6,10} := rep002 halph

theorem query414 (halph : AlphabetComplete link62 alphabets) : ActualObstruction link62 {3,6,10,11} :=
  obstruction_transport link62 FastDual62_002.points {3,6,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link62 alphabets) :
    ActualObstruction link62 FastDual62_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link62 rootCodes root_binding alphabets halph nonincident_complete
    FastDual62_003.pointList FastDual62_003.columns FastDual62_003.rows FastDual62_003.bound (by decide +kernel)
    FastDual62_003.column_mask FastDual62_003.checked hc F hF hroot hmin hout

theorem query218 (halph : AlphabetComplete link62 alphabets) : ActualObstruction link62 {1,3,6,11} := rep003 halph

theorem query274 (halph : AlphabetComplete link62 alphabets) : ActualObstruction link62 {1,6,10,11} :=
  obstruction_transport link62 FastDual62_003.points {1,6,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link62 alphabets) :
    ActualObstruction link62 FastDual62_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link62 rootCodes root_binding alphabets halph nonincident_complete
    FastDual62_004.pointList FastDual62_004.columns FastDual62_004.rows FastDual62_004.bound (by decide +kernel)
    FastDual62_004.column_mask FastDual62_004.checked hc F hF hroot hmin hout

theorem query253 (halph : AlphabetComplete link62 alphabets) : ActualObstruction link62 {1,5,6,10} := rep004 halph

theorem query394 (halph : AlphabetComplete link62 alphabets) : ActualObstruction link62 {3,5,6,11} :=
  obstruction_transport link62 FastDual62_004.points {3,5,6,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link62 alphabets) :
    ActualObstruction link62 FastDual62_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link62 rootCodes root_binding alphabets halph nonincident_complete
    FastDual62_005.pointList FastDual62_005.columns FastDual62_005.rows FastDual62_005.bound (by decide +kernel)
    FastDual62_005.column_mask FastDual62_005.checked hc F hF hroot hmin hout

theorem query254 (halph : AlphabetComplete link62 alphabets) : ActualObstruction link62 {1,5,6,11} := rep005 halph

theorem rep006 (halph : AlphabetComplete link62 alphabets) :
    ActualObstruction link62 FastDual62_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link62 rootCodes root_binding alphabets halph nonincident_complete
    FastDual62_006.pointList FastDual62_006.columns FastDual62_006.rows FastDual62_006.bound (by decide +kernel)
    FastDual62_006.column_mask FastDual62_006.checked hc F hF hroot hmin hout

theorem query393 (halph : AlphabetComplete link62 alphabets) : ActualObstruction link62 {3,5,6,10} := rep006 halph

def dualQuads : List (Finset Point) := [{1,3,5,10},{3,5,10,11},{1,3,5,11},{1,5,10,11},{1,3,6,10},{3,6,10,11},{1,3,6,11},{1,6,10,11},{1,5,6,10},{3,5,6,11},{1,5,6,11},{3,5,6,10}]

theorem dual_actual (halph : AlphabetComplete link62 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link62 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query212 halph
  · exact query404 halph
  · exact query213 halph
  · exact query264 halph
  · exact query217 halph
  · exact query414 halph
  · exact query218 halph
  · exact query274 halph
  · exact query253 halph
  · exact query394 halph
  · exact query254 halph
  · exact query393 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link62 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link62 Q :=
  class_census link62 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source62
