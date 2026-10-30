import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source44
import C13Global.FastGroups.Source44Part00
namespace C13.Global.Relative.Source44
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source44
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link44 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link44 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link44 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link44 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link44 alphabets) :
    ActualObstruction link44 FastDual44_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link44 rootCodes root_binding alphabets halph nonincident_complete
    FastDual44_000.pointList FastDual44_000.columns FastDual44_000.rows FastDual44_000.bound (by decide +kernel)
    FastDual44_000.column_mask FastDual44_000.checked hc F hF hroot hmin hout

theorem query303 (halph : AlphabetComplete link44 alphabets) : ActualObstruction link44 {2,3,7,8} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link44 = link44 :=
  root_symmetry_of_codes rootCodes link44 root_binding automorphism000 (by decide +kernel)

theorem query304 (halph : AlphabetComplete link44 alphabets) : ActualObstruction link44 {2,3,7,9} :=
  obstruction_transport link44 FastDual44_000.points {2,3,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link44 alphabets) :
    ActualObstruction link44 FastDual44_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link44 rootCodes root_binding alphabets halph nonincident_complete
    FastDual44_001.pointList FastDual44_001.columns FastDual44_001.rows FastDual44_001.bound (by decide +kernel)
    FastDual44_001.column_mask FastDual44_001.checked hc F hF hroot hmin hout

theorem query306 (halph : AlphabetComplete link44 alphabets) : ActualObstruction link44 {2,3,7,11} := rep001 halph

theorem rep002 (halph : AlphabetComplete link44 alphabets) :
    ActualObstruction link44 FastDual44_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link44 rootCodes root_binding alphabets halph nonincident_complete
    FastDual44_002.pointList FastDual44_002.columns FastDual44_002.rows FastDual44_002.bound (by decide +kernel)
    FastDual44_002.column_mask FastDual44_002.checked hc F hF hroot hmin hout

theorem query307 (halph : AlphabetComplete link44 alphabets) : ActualObstruction link44 {2,3,8,9} := rep002 halph

theorem rep003 (halph : AlphabetComplete link44 alphabets) :
    ActualObstruction link44 FastDual44_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link44 rootCodes root_binding alphabets halph nonincident_complete
    FastDual44_003.pointList FastDual44_003.columns FastDual44_003.rows FastDual44_003.bound (by decide +kernel)
    FastDual44_003.column_mask FastDual44_003.checked hc F hF hroot hmin hout

theorem query359 (halph : AlphabetComplete link44 alphabets) : ActualObstruction link44 {2,7,8,9} := rep003 halph

theorem query415 (halph : AlphabetComplete link44 alphabets) : ActualObstruction link44 {3,7,8,9} :=
  obstruction_transport link44 FastDual44_003.points {3,7,8,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link44 alphabets) :
    ActualObstruction link44 FastDual44_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link44 rootCodes root_binding alphabets halph nonincident_complete
    FastDual44_004.pointList FastDual44_004.columns FastDual44_004.rows FastDual44_004.bound (by decide +kernel)
    FastDual44_004.column_mask FastDual44_004.checked hc F hF hroot hmin hout

theorem query361 (halph : AlphabetComplete link44 alphabets) : ActualObstruction link44 {2,7,8,11} := rep004 halph

theorem query419 (halph : AlphabetComplete link44 alphabets) : ActualObstruction link44 {3,7,9,11} :=
  obstruction_transport link44 FastDual44_004.points {3,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link44 alphabets) :
    ActualObstruction link44 FastDual44_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link44 rootCodes root_binding alphabets halph nonincident_complete
    FastDual44_005.pointList FastDual44_005.columns FastDual44_005.rows FastDual44_005.bound (by decide +kernel)
    FastDual44_005.column_mask FastDual44_005.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link44 alphabets) : ActualObstruction link44 {2,7,9,11} := rep005 halph

theorem query417 (halph : AlphabetComplete link44 alphabets) : ActualObstruction link44 {3,7,8,11} :=
  obstruction_transport link44 FastDual44_005.points {3,7,8,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

def dualQuads : List (Finset Point) := [{2,3,7,8},{2,3,7,9},{2,3,7,11},{2,3,8,9},{2,7,8,9},{3,7,8,9},{2,7,8,11},{3,7,9,11},{2,7,9,11},{3,7,8,11}]

theorem dual_actual (halph : AlphabetComplete link44 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link44 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query303 halph
  · exact query304 halph
  · exact query306 halph
  · exact query307 halph
  · exact query359 halph
  · exact query415 halph
  · exact query361 halph
  · exact query419 halph
  · exact query363 halph
  · exact query417 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link44 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link44 Q :=
  class_census link44 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source44
