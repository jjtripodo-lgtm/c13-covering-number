import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source54
import C13Global.FastGroups.Source54Part00
import C13Global.FastGroups.Source54Part01
namespace C13.Global.Relative.Source54
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source54
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link54 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link54 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link54 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link54 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link54 alphabets) :
    ActualObstruction link54 FastDual54_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link54 rootCodes root_binding alphabets halph nonincident_complete
    FastDual54_000.pointList FastDual54_000.columns FastDual54_000.rows FastDual54_000.bound (by decide +kernel)
    FastDual54_000.column_mask FastDual54_000.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,3,6,7} := rep000 halph

theorem rep001 (halph : AlphabetComplete link54 alphabets) :
    ActualObstruction link54 FastDual54_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link54 rootCodes root_binding alphabets halph nonincident_complete
    FastDual54_001.pointList FastDual54_001.columns FastDual54_001.rows FastDual54_001.bound (by decide +kernel)
    FastDual54_001.column_mask FastDual54_001.checked hc F hF hroot hmin hout

theorem query300 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,3,6,9} := rep001 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link54 = link54 :=
  root_symmetry_of_codes rootCodes link54 root_binding automorphism000 (by decide +kernel)

theorem query304 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,3,7,9} :=
  obstruction_transport link54 FastDual54_001.points {2,3,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

def automorphism001 : Equiv.Perm Point where
  toFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  invFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism001_hole : automorphism001 hole = hole := by decide +kernel

theorem automorphism001_root : transport automorphism001 link54 = link54 :=
  root_symmetry_of_codes rootCodes link54 root_binding automorphism001 (by decide +kernel)

theorem query350 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,6,7,9} :=
  obstruction_transport link54 FastDual54_001.points {2,6,7,9} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep001 halph)

def automorphism002 : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  invFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism002_hole : automorphism002 hole = hole := by decide +kernel

theorem automorphism002_root : transport automorphism002 link54 = link54 :=
  root_symmetry_of_codes rootCodes link54 root_binding automorphism002 (by decide +kernel)

theorem query406 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {3,6,7,9} :=
  obstruction_transport link54 FastDual54_001.points {3,6,7,9} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link54 alphabets) :
    ActualObstruction link54 FastDual54_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link54 rootCodes root_binding alphabets halph nonincident_complete
    FastDual54_002.pointList FastDual54_002.columns FastDual54_002.rows FastDual54_002.bound (by decide +kernel)
    FastDual54_002.column_mask FastDual54_002.checked hc F hF hroot hmin hout

theorem query301 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,3,6,10} := rep002 halph

theorem query306 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,3,7,11} :=
  obstruction_transport link54 FastDual54_002.points {2,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem query351 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,6,7,10} :=
  obstruction_transport link54 FastDual54_002.points {2,6,7,10} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep002 halph)

theorem query408 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {3,6,7,11} :=
  obstruction_transport link54 FastDual54_002.points {3,6,7,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link54 alphabets) :
    ActualObstruction link54 FastDual54_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link54 rootCodes root_binding alphabets halph nonincident_complete
    FastDual54_003.pointList FastDual54_003.columns FastDual54_003.rows FastDual54_003.bound (by decide +kernel)
    FastDual54_003.column_mask FastDual54_003.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,3,6,11} := rep003 halph

theorem query305 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,3,7,10} :=
  obstruction_transport link54 FastDual54_003.points {2,3,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem query352 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,6,7,11} :=
  obstruction_transport link54 FastDual54_003.points {2,6,7,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep003 halph)

theorem query407 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {3,6,7,10} :=
  obstruction_transport link54 FastDual54_003.points {3,6,7,10} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link54 alphabets) :
    ActualObstruction link54 FastDual54_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link54 rootCodes root_binding alphabets halph nonincident_complete
    FastDual54_004.pointList FastDual54_004.columns FastDual54_004.rows FastDual54_004.bound (by decide +kernel)
    FastDual54_004.column_mask FastDual54_004.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,3,10,11} := rep004 halph

theorem query485 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {6,7,10,11} :=
  obstruction_transport link54 FastDual54_004.points {6,7,10,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link54 alphabets) :
    ActualObstruction link54 FastDual54_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link54 rootCodes root_binding alphabets halph nonincident_complete
    FastDual54_005.pointList FastDual54_005.columns FastDual54_005.rows FastDual54_005.bound (by decide +kernel)
    FastDual54_005.column_mask FastDual54_005.checked hc F hF hroot hmin hout

theorem query356 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,6,9,10} := rep005 halph

theorem query419 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {3,7,9,11} :=
  obstruction_transport link54 FastDual54_005.points {3,7,9,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link54 alphabets) :
    ActualObstruction link54 FastDual54_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link54 rootCodes root_binding alphabets halph nonincident_complete
    FastDual54_006.pointList FastDual54_006.columns FastDual54_006.rows FastDual54_006.bound (by decide +kernel)
    FastDual54_006.column_mask FastDual54_006.checked hc F hF hroot hmin hout

theorem query357 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,6,9,11} := rep006 halph

theorem query418 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {3,7,9,10} :=
  obstruction_transport link54 FastDual54_006.points {3,7,9,10} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link54 alphabets) :
    ActualObstruction link54 FastDual54_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link54 rootCodes root_binding alphabets halph nonincident_complete
    FastDual54_007.pointList FastDual54_007.columns FastDual54_007.rows FastDual54_007.bound (by decide +kernel)
    FastDual54_007.column_mask FastDual54_007.checked hc F hF hroot hmin hout

theorem query358 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,6,10,11} := rep007 halph

theorem query420 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {3,7,10,11} :=
  obstruction_transport link54 FastDual54_007.points {3,7,10,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link54 alphabets) :
    ActualObstruction link54 FastDual54_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link54 rootCodes root_binding alphabets halph nonincident_complete
    FastDual54_008.pointList FastDual54_008.columns FastDual54_008.rows FastDual54_008.bound (by decide +kernel)
    FastDual54_008.column_mask FastDual54_008.checked hc F hF hroot hmin hout

theorem query362 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,7,9,10} := rep008 halph

theorem query363 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,7,9,11} :=
  obstruction_transport link54 FastDual54_008.points {2,7,9,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep008 halph)

theorem query412 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {3,6,9,10} :=
  obstruction_transport link54 FastDual54_008.points {3,6,9,10} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep008 halph)

theorem query413 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {3,6,9,11} :=
  obstruction_transport link54 FastDual54_008.points {3,6,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link54 alphabets) :
    ActualObstruction link54 FastDual54_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link54 rootCodes root_binding alphabets halph nonincident_complete
    FastDual54_009.pointList FastDual54_009.columns FastDual54_009.rows FastDual54_009.bound (by decide +kernel)
    FastDual54_009.column_mask FastDual54_009.checked hc F hF hroot hmin hout

theorem query364 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {2,7,10,11} := rep009 halph

theorem query414 (halph : AlphabetComplete link54 alphabets) : ActualObstruction link54 {3,6,10,11} :=
  obstruction_transport link54 FastDual54_009.points {3,6,10,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep009 halph)

def dualQuads : List (Finset Point) := [{2,3,6,7},{2,3,6,9},{2,3,7,9},{2,6,7,9},{3,6,7,9},{2,3,6,10},{2,3,7,11},{2,6,7,10},{3,6,7,11},{2,3,6,11},{2,3,7,10},{2,6,7,11},{3,6,7,10},{2,3,10,11},{6,7,10,11},{2,6,9,10},{3,7,9,11},{2,6,9,11},{3,7,9,10},{2,6,10,11},{3,7,10,11},{2,7,9,10},{2,7,9,11},{3,6,9,10},{3,6,9,11},{2,7,10,11},{3,6,10,11}]

theorem dual_actual (halph : AlphabetComplete link54 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link54 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query298 halph
  · exact query300 halph
  · exact query304 halph
  · exact query350 halph
  · exact query406 halph
  · exact query301 halph
  · exact query306 halph
  · exact query351 halph
  · exact query408 halph
  · exact query302 halph
  · exact query305 halph
  · exact query352 halph
  · exact query407 halph
  · exact query312 halph
  · exact query485 halph
  · exact query356 halph
  · exact query419 halph
  · exact query357 halph
  · exact query418 halph
  · exact query358 halph
  · exact query420 halph
  · exact query362 halph
  · exact query363 halph
  · exact query412 halph
  · exact query413 halph
  · exact query364 halph
  · exact query414 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link54 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link54 Q :=
  class_census link54 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source54
