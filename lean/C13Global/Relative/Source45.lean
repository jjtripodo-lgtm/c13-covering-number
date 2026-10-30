import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source45
import C13Global.FastGroups.Source45Part00
namespace C13.Global.Relative.Source45
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source45
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link45 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link45 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link45 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link45 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link45 alphabets) :
    ActualObstruction link45 FastDual45_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link45 rootCodes root_binding alphabets halph nonincident_complete
    FastDual45_000.pointList FastDual45_000.columns FastDual45_000.rows FastDual45_000.bound (by decide +kernel)
    FastDual45_000.column_mask FastDual45_000.checked hc F hF hroot hmin hout

theorem query299 (halph : AlphabetComplete link45 alphabets) : ActualObstruction link45 {2,3,6,8} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link45 = link45 :=
  root_symmetry_of_codes rootCodes link45 root_binding automorphism000 (by decide +kernel)

theorem query300 (halph : AlphabetComplete link45 alphabets) : ActualObstruction link45 {2,3,6,9} :=
  obstruction_transport link45 FastDual45_000.points {2,3,6,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link45 alphabets) :
    ActualObstruction link45 FastDual45_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link45 rootCodes root_binding alphabets halph nonincident_complete
    FastDual45_001.pointList FastDual45_001.columns FastDual45_001.rows FastDual45_001.bound (by decide +kernel)
    FastDual45_001.column_mask FastDual45_001.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link45 alphabets) : ActualObstruction link45 {2,3,6,11} := rep001 halph

theorem rep002 (halph : AlphabetComplete link45 alphabets) :
    ActualObstruction link45 FastDual45_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link45 rootCodes root_binding alphabets halph nonincident_complete
    FastDual45_002.pointList FastDual45_002.columns FastDual45_002.rows FastDual45_002.bound (by decide +kernel)
    FastDual45_002.column_mask FastDual45_002.checked hc F hF hroot hmin hout

theorem query307 (halph : AlphabetComplete link45 alphabets) : ActualObstruction link45 {2,3,8,9} := rep002 halph

theorem rep003 (halph : AlphabetComplete link45 alphabets) :
    ActualObstruction link45 FastDual45_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link45 rootCodes root_binding alphabets halph nonincident_complete
    FastDual45_003.pointList FastDual45_003.columns FastDual45_003.rows FastDual45_003.bound (by decide +kernel)
    FastDual45_003.column_mask FastDual45_003.checked hc F hF hroot hmin hout

theorem query353 (halph : AlphabetComplete link45 alphabets) : ActualObstruction link45 {2,6,8,9} := rep003 halph

theorem query409 (halph : AlphabetComplete link45 alphabets) : ActualObstruction link45 {3,6,8,9} :=
  obstruction_transport link45 FastDual45_003.points {3,6,8,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link45 alphabets) :
    ActualObstruction link45 FastDual45_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link45 rootCodes root_binding alphabets halph nonincident_complete
    FastDual45_004.pointList FastDual45_004.columns FastDual45_004.rows FastDual45_004.bound (by decide +kernel)
    FastDual45_004.column_mask FastDual45_004.checked hc F hF hroot hmin hout

theorem query355 (halph : AlphabetComplete link45 alphabets) : ActualObstruction link45 {2,6,8,11} := rep004 halph

theorem query413 (halph : AlphabetComplete link45 alphabets) : ActualObstruction link45 {3,6,9,11} :=
  obstruction_transport link45 FastDual45_004.points {3,6,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link45 alphabets) :
    ActualObstruction link45 FastDual45_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link45 rootCodes root_binding alphabets halph nonincident_complete
    FastDual45_005.pointList FastDual45_005.columns FastDual45_005.rows FastDual45_005.bound (by decide +kernel)
    FastDual45_005.column_mask FastDual45_005.checked hc F hF hroot hmin hout

theorem query357 (halph : AlphabetComplete link45 alphabets) : ActualObstruction link45 {2,6,9,11} := rep005 halph

theorem query411 (halph : AlphabetComplete link45 alphabets) : ActualObstruction link45 {3,6,8,11} :=
  obstruction_transport link45 FastDual45_005.points {3,6,8,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link45 alphabets) :
    ActualObstruction link45 FastDual45_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link45 rootCodes root_binding alphabets halph nonincident_complete
    FastDual45_006.pointList FastDual45_006.columns FastDual45_006.rows FastDual45_006.bound (by decide +kernel)
    FastDual45_006.column_mask FastDual45_006.checked hc F hF hroot hmin hout

theorem query487 (halph : AlphabetComplete link45 alphabets) : ActualObstruction link45 {6,8,9,11} := rep006 halph

def dualQuads : List (Finset Point) := [{2,3,6,8},{2,3,6,9},{2,3,6,11},{2,3,8,9},{2,6,8,9},{3,6,8,9},{2,6,8,11},{3,6,9,11},{2,6,9,11},{3,6,8,11},{6,8,9,11}]

theorem dual_actual (halph : AlphabetComplete link45 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link45 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query299 halph
  · exact query300 halph
  · exact query302 halph
  · exact query307 halph
  · exact query353 halph
  · exact query409 halph
  · exact query355 halph
  · exact query413 halph
  · exact query357 halph
  · exact query411 halph
  · exact query487 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link45 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link45 Q :=
  class_census link45 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source45
