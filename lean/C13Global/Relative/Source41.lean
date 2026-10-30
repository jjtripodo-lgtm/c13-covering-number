import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source41
import C13Global.FastGroups.Source41Part00
import C13Global.FastGroups.Source41Part01
namespace C13.Global.Relative.Source41
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source41
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link41 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link41 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link41 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link41 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link41 alphabets) :
    ActualObstruction link41 FastDual41_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link41 rootCodes root_binding alphabets halph nonincident_complete
    FastDual41_000.pointList FastDual41_000.columns FastDual41_000.rows FastDual41_000.bound (by decide +kernel)
    FastDual41_000.column_mask FastDual41_000.checked hc F hF hroot hmin hout

theorem query191 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {1,2,7,8} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link41 = link41 :=
  root_symmetry_of_codes rootCodes link41 root_binding automorphism000 (by decide +kernel)

theorem query220 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {1,3,7,9} :=
  obstruction_transport link41 FastDual41_000.points {1,3,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link41 alphabets) :
    ActualObstruction link41 FastDual41_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link41 rootCodes root_binding alphabets halph nonincident_complete
    FastDual41_001.pointList FastDual41_001.columns FastDual41_001.rows FastDual41_001.bound (by decide +kernel)
    FastDual41_001.column_mask FastDual41_001.checked hc F hF hroot hmin hout

theorem query192 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {1,2,7,9} := rep001 halph

theorem query219 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {1,3,7,8} :=
  obstruction_transport link41 FastDual41_001.points {1,3,7,8} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link41 alphabets) :
    ActualObstruction link41 FastDual41_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link41 rootCodes root_binding alphabets halph nonincident_complete
    FastDual41_002.pointList FastDual41_002.columns FastDual41_002.rows FastDual41_002.bound (by decide +kernel)
    FastDual41_002.column_mask FastDual41_002.checked hc F hF hroot hmin hout

theorem query194 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {1,2,7,11} := rep002 halph

theorem query222 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {1,3,7,11} :=
  obstruction_transport link41 FastDual41_002.points {1,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link41 alphabets) :
    ActualObstruction link41 FastDual41_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link41 rootCodes root_binding alphabets halph nonincident_complete
    FastDual41_003.pointList FastDual41_003.columns FastDual41_003.rows FastDual41_003.bound (by decide +kernel)
    FastDual41_003.column_mask FastDual41_003.checked hc F hF hroot hmin hout

theorem query197 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {1,2,8,11} := rep003 halph

theorem query227 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {1,3,9,11} :=
  obstruction_transport link41 FastDual41_003.points {1,3,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link41 alphabets) :
    ActualObstruction link41 FastDual41_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link41 rootCodes root_binding alphabets halph nonincident_complete
    FastDual41_004.pointList FastDual41_004.columns FastDual41_004.rows FastDual41_004.bound (by decide +kernel)
    FastDual41_004.column_mask FastDual41_004.checked hc F hF hroot hmin hout

theorem query275 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {1,7,8,9} := rep004 halph

theorem rep005 (halph : AlphabetComplete link41 alphabets) :
    ActualObstruction link41 FastDual41_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link41 rootCodes root_binding alphabets halph nonincident_complete
    FastDual41_005.pointList FastDual41_005.columns FastDual41_005.rows FastDual41_005.bound (by decide +kernel)
    FastDual41_005.column_mask FastDual41_005.checked hc F hF hroot hmin hout

theorem query277 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {1,7,8,11} := rep005 halph

theorem query279 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {1,7,9,11} :=
  obstruction_transport link41 FastDual41_005.points {1,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link41 alphabets) :
    ActualObstruction link41 FastDual41_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link41 rootCodes root_binding alphabets halph nonincident_complete
    FastDual41_006.pointList FastDual41_006.columns FastDual41_006.rows FastDual41_006.bound (by decide +kernel)
    FastDual41_006.column_mask FastDual41_006.checked hc F hF hroot hmin hout

theorem query303 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {2,3,7,8} := rep006 halph

theorem query304 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {2,3,7,9} :=
  obstruction_transport link41 FastDual41_006.points {2,3,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link41 alphabets) :
    ActualObstruction link41 FastDual41_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link41 rootCodes root_binding alphabets halph nonincident_complete
    FastDual41_007.pointList FastDual41_007.columns FastDual41_007.rows FastDual41_007.bound (by decide +kernel)
    FastDual41_007.column_mask FastDual41_007.checked hc F hF hroot hmin hout

theorem query306 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {2,3,7,11} := rep007 halph

theorem rep008 (halph : AlphabetComplete link41 alphabets) :
    ActualObstruction link41 FastDual41_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link41 rootCodes root_binding alphabets halph nonincident_complete
    FastDual41_008.pointList FastDual41_008.columns FastDual41_008.rows FastDual41_008.bound (by decide +kernel)
    FastDual41_008.column_mask FastDual41_008.checked hc F hF hroot hmin hout

theorem query307 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {2,3,8,9} := rep008 halph

theorem rep009 (halph : AlphabetComplete link41 alphabets) :
    ActualObstruction link41 FastDual41_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link41 rootCodes root_binding alphabets halph nonincident_complete
    FastDual41_009.pointList FastDual41_009.columns FastDual41_009.rows FastDual41_009.bound (by decide +kernel)
    FastDual41_009.column_mask FastDual41_009.checked hc F hF hroot hmin hout

theorem query359 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {2,7,8,9} := rep009 halph

theorem query415 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {3,7,8,9} :=
  obstruction_transport link41 FastDual41_009.points {3,7,8,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link41 alphabets) :
    ActualObstruction link41 FastDual41_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link41 rootCodes root_binding alphabets halph nonincident_complete
    FastDual41_010.pointList FastDual41_010.columns FastDual41_010.rows FastDual41_010.bound (by decide +kernel)
    FastDual41_010.column_mask FastDual41_010.checked hc F hF hroot hmin hout

theorem query361 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {2,7,8,11} := rep010 halph

theorem query419 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {3,7,9,11} :=
  obstruction_transport link41 FastDual41_010.points {3,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link41 alphabets) :
    ActualObstruction link41 FastDual41_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link41 rootCodes root_binding alphabets halph nonincident_complete
    FastDual41_011.pointList FastDual41_011.columns FastDual41_011.rows FastDual41_011.bound (by decide +kernel)
    FastDual41_011.column_mask FastDual41_011.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {2,7,9,11} := rep011 halph

theorem query417 (halph : AlphabetComplete link41 alphabets) : ActualObstruction link41 {3,7,8,11} :=
  obstruction_transport link41 FastDual41_011.points {3,7,8,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep011 halph)

def dualQuads : List (Finset Point) := [{1,2,7,8},{1,3,7,9},{1,2,7,9},{1,3,7,8},{1,2,7,11},{1,3,7,11},{1,2,8,11},{1,3,9,11},{1,7,8,9},{1,7,8,11},{1,7,9,11},{2,3,7,8},{2,3,7,9},{2,3,7,11},{2,3,8,9},{2,7,8,9},{3,7,8,9},{2,7,8,11},{3,7,9,11},{2,7,9,11},{3,7,8,11}]

theorem dual_actual (halph : AlphabetComplete link41 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link41 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query191 halph
  · exact query220 halph
  · exact query192 halph
  · exact query219 halph
  · exact query194 halph
  · exact query222 halph
  · exact query197 halph
  · exact query227 halph
  · exact query275 halph
  · exact query277 halph
  · exact query279 halph
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

theorem all_foursets (halph : AlphabetComplete link41 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link41 Q :=
  class_census link41 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source41
