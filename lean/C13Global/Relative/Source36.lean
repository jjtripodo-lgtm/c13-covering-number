import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source36
import C13Global.FastGroups.Source36Part00
import C13Global.FastGroups.Source36Part01
namespace C13.Global.Relative.Source36
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source36
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link36 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link36 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link36 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link36 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link36 alphabets) :
    ActualObstruction link36 FastDual36_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link36 rootCodes root_binding alphabets halph nonincident_complete
    FastDual36_000.pointList FastDual36_000.columns FastDual36_000.rows FastDual36_000.bound (by decide +kernel)
    FastDual36_000.column_mask FastDual36_000.checked hc F hF hroot hmin hout

theorem query188 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,2,6,9} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link36 = link36 :=
  root_symmetry_of_codes rootCodes link36 root_binding automorphism000 (by decide +kernel)

theorem query220 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,3,7,9} :=
  obstruction_transport link36 FastDual36_000.points {1,3,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

def automorphism001 : Equiv.Perm Point where
  toFun := ![8,9,10,11,4,5,6,7,0,1,2,3,12]
  invFun := ![8,9,10,11,4,5,6,7,0,1,2,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism001_hole : automorphism001 hole = hole := by decide +kernel

theorem automorphism001_root : transport automorphism001 link36 = link36 :=
  root_symmetry_of_codes rootCodes link36 root_binding automorphism001 (by decide +kernel)

theorem query272 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,6,9,10} :=
  obstruction_transport link36 FastDual36_000.points {1,6,9,10} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep000 halph)

def automorphism002 : Equiv.Perm Point where
  toFun := ![8,9,11,10,4,5,7,6,0,1,3,2,12]
  invFun := ![8,9,11,10,4,5,7,6,0,1,3,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism002_hole : automorphism002 hole = hole := by decide +kernel

theorem automorphism002_root : transport automorphism002 link36 = link36 :=
  root_symmetry_of_codes rootCodes link36 root_binding automorphism002 (by decide +kernel)

theorem query279 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,7,9,11} :=
  obstruction_transport link36 FastDual36_000.points {1,7,9,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link36 alphabets) :
    ActualObstruction link36 FastDual36_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link36 rootCodes root_binding alphabets halph nonincident_complete
    FastDual36_001.pointList FastDual36_001.columns FastDual36_001.rows FastDual36_001.bound (by decide +kernel)
    FastDual36_001.column_mask FastDual36_001.checked hc F hF hroot hmin hout

theorem query189 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,2,6,10} := rep001 halph

theorem query222 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,3,7,11} :=
  obstruction_transport link36 FastDual36_001.points {1,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

theorem query356 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,6,9,10} :=
  obstruction_transport link36 FastDual36_001.points {2,6,9,10} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep001 halph)

theorem query419 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {3,7,9,11} :=
  obstruction_transport link36 FastDual36_001.points {3,7,9,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link36 alphabets) :
    ActualObstruction link36 FastDual36_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link36 rootCodes root_binding alphabets halph nonincident_complete
    FastDual36_002.pointList FastDual36_002.columns FastDual36_002.rows FastDual36_002.bound (by decide +kernel)
    FastDual36_002.column_mask FastDual36_002.checked hc F hF hroot hmin hout

theorem query190 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,2,6,11} := rep002 halph

theorem query221 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,3,7,10} :=
  obstruction_transport link36 FastDual36_002.points {1,3,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem query363 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,7,9,11} :=
  obstruction_transport link36 FastDual36_002.points {2,7,9,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep002 halph)

theorem query412 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {3,6,9,10} :=
  obstruction_transport link36 FastDual36_002.points {3,6,9,10} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link36 alphabets) :
    ActualObstruction link36 FastDual36_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link36 rootCodes root_binding alphabets halph nonincident_complete
    FastDual36_003.pointList FastDual36_003.columns FastDual36_003.rows FastDual36_003.bound (by decide +kernel)
    FastDual36_003.column_mask FastDual36_003.checked hc F hF hroot hmin hout

theorem query192 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,2,7,9} := rep003 halph

theorem query216 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,3,6,9} :=
  obstruction_transport link36 FastDual36_003.points {1,3,6,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem query273 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,6,9,11} :=
  obstruction_transport link36 FastDual36_003.points {1,6,9,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep003 halph)

theorem query278 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,7,9,10} :=
  obstruction_transport link36 FastDual36_003.points {1,7,9,10} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link36 alphabets) :
    ActualObstruction link36 FastDual36_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link36 rootCodes root_binding alphabets halph nonincident_complete
    FastDual36_004.pointList FastDual36_004.columns FastDual36_004.rows FastDual36_004.bound (by decide +kernel)
    FastDual36_004.column_mask FastDual36_004.checked hc F hF hroot hmin hout

theorem query193 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,2,7,10} := rep004 halph

theorem query218 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,3,6,11} :=
  obstruction_transport link36 FastDual36_004.points {1,3,6,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep004 halph)

theorem query362 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,7,9,10} :=
  obstruction_transport link36 FastDual36_004.points {2,7,9,10} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep004 halph)

theorem query413 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {3,6,9,11} :=
  obstruction_transport link36 FastDual36_004.points {3,6,9,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link36 alphabets) :
    ActualObstruction link36 FastDual36_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link36 rootCodes root_binding alphabets halph nonincident_complete
    FastDual36_005.pointList FastDual36_005.columns FastDual36_005.rows FastDual36_005.bound (by decide +kernel)
    FastDual36_005.column_mask FastDual36_005.checked hc F hF hroot hmin hout

theorem query194 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,2,7,11} := rep005 halph

theorem query217 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,3,6,10} :=
  obstruction_transport link36 FastDual36_005.points {1,3,6,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem query357 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,6,9,11} :=
  obstruction_transport link36 FastDual36_005.points {2,6,9,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep005 halph)

theorem query418 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {3,7,9,10} :=
  obstruction_transport link36 FastDual36_005.points {3,7,9,10} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link36 alphabets) :
    ActualObstruction link36 FastDual36_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link36 rootCodes root_binding alphabets halph nonincident_complete
    FastDual36_006.pointList FastDual36_006.columns FastDual36_006.rows FastDual36_006.bound (by decide +kernel)
    FastDual36_006.column_mask FastDual36_006.checked hc F hF hroot hmin hout

theorem query198 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,2,9,10} := rep006 halph

theorem query227 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,3,9,11} :=
  obstruction_transport link36 FastDual36_006.points {1,3,9,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link36 alphabets) :
    ActualObstruction link36 FastDual36_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link36 rootCodes root_binding alphabets halph nonincident_complete
    FastDual36_007.pointList FastDual36_007.columns FastDual36_007.rows FastDual36_007.bound (by decide +kernel)
    FastDual36_007.column_mask FastDual36_007.checked hc F hF hroot hmin hout

theorem query266 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,6,7,9} := rep007 halph

theorem rep008 (halph : AlphabetComplete link36 alphabets) :
    ActualObstruction link36 FastDual36_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link36 rootCodes root_binding alphabets halph nonincident_complete
    FastDual36_008.pointList FastDual36_008.columns FastDual36_008.rows FastDual36_008.bound (by decide +kernel)
    FastDual36_008.column_mask FastDual36_008.checked hc F hF hroot hmin hout

theorem query267 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,6,7,10} := rep008 halph

theorem query268 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,6,7,11} :=
  obstruction_transport link36 FastDual36_008.points {1,6,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep008 halph)

theorem query350 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,6,7,9} :=
  obstruction_transport link36 FastDual36_008.points {2,6,7,9} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep008 halph)

theorem query406 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {3,6,7,9} :=
  obstruction_transport link36 FastDual36_008.points {3,6,7,9} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link36 alphabets) :
    ActualObstruction link36 FastDual36_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link36 rootCodes root_binding alphabets halph nonincident_complete
    FastDual36_009.pointList FastDual36_009.columns FastDual36_009.rows FastDual36_009.bound (by decide +kernel)
    FastDual36_009.column_mask FastDual36_009.checked hc F hF hroot hmin hout

theorem query274 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,6,10,11} := rep009 halph

theorem query280 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {1,7,10,11} :=
  obstruction_transport link36 FastDual36_009.points {1,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep009 halph)

theorem query300 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,3,6,9} :=
  obstruction_transport link36 FastDual36_009.points {2,3,6,9} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep009 halph)

theorem query304 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,3,7,9} :=
  obstruction_transport link36 FastDual36_009.points {2,3,7,9} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link36 alphabets) :
    ActualObstruction link36 FastDual36_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link36 rootCodes root_binding alphabets halph nonincident_complete
    FastDual36_010.pointList FastDual36_010.columns FastDual36_010.rows FastDual36_010.bound (by decide +kernel)
    FastDual36_010.column_mask FastDual36_010.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,3,6,7} := rep010 halph

theorem query485 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {6,7,10,11} :=
  obstruction_transport link36 FastDual36_010.points {6,7,10,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link36 alphabets) :
    ActualObstruction link36 FastDual36_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link36 rootCodes root_binding alphabets halph nonincident_complete
    FastDual36_011.pointList FastDual36_011.columns FastDual36_011.rows FastDual36_011.bound (by decide +kernel)
    FastDual36_011.column_mask FastDual36_011.checked hc F hF hroot hmin hout

theorem query301 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,3,6,10} := rep011 halph

theorem query306 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,3,7,11} :=
  obstruction_transport link36 FastDual36_011.points {2,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep011 halph)

theorem query358 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,6,10,11} :=
  obstruction_transport link36 FastDual36_011.points {2,6,10,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep011 halph)

theorem query420 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {3,7,10,11} :=
  obstruction_transport link36 FastDual36_011.points {3,7,10,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link36 alphabets) :
    ActualObstruction link36 FastDual36_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link36 rootCodes root_binding alphabets halph nonincident_complete
    FastDual36_012.pointList FastDual36_012.columns FastDual36_012.rows FastDual36_012.bound (by decide +kernel)
    FastDual36_012.column_mask FastDual36_012.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,3,6,11} := rep012 halph

theorem query305 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,3,7,10} :=
  obstruction_transport link36 FastDual36_012.points {2,3,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep012 halph)

theorem query364 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,7,10,11} :=
  obstruction_transport link36 FastDual36_012.points {2,7,10,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep012 halph)

theorem query414 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {3,6,10,11} :=
  obstruction_transport link36 FastDual36_012.points {3,6,10,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep012 halph)

theorem rep013 (halph : AlphabetComplete link36 alphabets) :
    ActualObstruction link36 FastDual36_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link36 rootCodes root_binding alphabets halph nonincident_complete
    FastDual36_013.pointList FastDual36_013.columns FastDual36_013.rows FastDual36_013.bound (by decide +kernel)
    FastDual36_013.column_mask FastDual36_013.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,3,10,11} := rep013 halph

theorem rep014 (halph : AlphabetComplete link36 alphabets) :
    ActualObstruction link36 FastDual36_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link36 rootCodes root_binding alphabets halph nonincident_complete
    FastDual36_014.pointList FastDual36_014.columns FastDual36_014.rows FastDual36_014.bound (by decide +kernel)
    FastDual36_014.column_mask FastDual36_014.checked hc F hF hroot hmin hout

theorem query351 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,6,7,10} := rep014 halph

theorem query408 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {3,6,7,11} :=
  obstruction_transport link36 FastDual36_014.points {3,6,7,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep014 halph)

theorem rep015 (halph : AlphabetComplete link36 alphabets) :
    ActualObstruction link36 FastDual36_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link36 rootCodes root_binding alphabets halph nonincident_complete
    FastDual36_015.pointList FastDual36_015.columns FastDual36_015.rows FastDual36_015.bound (by decide +kernel)
    FastDual36_015.column_mask FastDual36_015.checked hc F hF hroot hmin hout

theorem query352 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {2,6,7,11} := rep015 halph

theorem query407 (halph : AlphabetComplete link36 alphabets) : ActualObstruction link36 {3,6,7,10} :=
  obstruction_transport link36 FastDual36_015.points {3,6,7,10} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep015 halph)

def dualQuads : List (Finset Point) := [{1,2,6,9},{1,3,7,9},{1,6,9,10},{1,7,9,11},{1,2,6,10},{1,3,7,11},{2,6,9,10},{3,7,9,11},{1,2,6,11},{1,3,7,10},{2,7,9,11},{3,6,9,10},{1,2,7,9},{1,3,6,9},{1,6,9,11},{1,7,9,10},{1,2,7,10},{1,3,6,11},{2,7,9,10},{3,6,9,11},{1,2,7,11},{1,3,6,10},{2,6,9,11},{3,7,9,10},{1,2,9,10},{1,3,9,11},{1,6,7,9},{1,6,7,10},{1,6,7,11},{2,6,7,9},{3,6,7,9},{1,6,10,11},{1,7,10,11},{2,3,6,9},{2,3,7,9},{2,3,6,7},{6,7,10,11},{2,3,6,10},{2,3,7,11},{2,6,10,11},{3,7,10,11},{2,3,6,11},{2,3,7,10},{2,7,10,11},{3,6,10,11},{2,3,10,11},{2,6,7,10},{3,6,7,11},{2,6,7,11},{3,6,7,10}]

theorem dual_actual (halph : AlphabetComplete link36 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link36 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query188 halph
  · exact query220 halph
  · exact query272 halph
  · exact query279 halph
  · exact query189 halph
  · exact query222 halph
  · exact query356 halph
  · exact query419 halph
  · exact query190 halph
  · exact query221 halph
  · exact query363 halph
  · exact query412 halph
  · exact query192 halph
  · exact query216 halph
  · exact query273 halph
  · exact query278 halph
  · exact query193 halph
  · exact query218 halph
  · exact query362 halph
  · exact query413 halph
  · exact query194 halph
  · exact query217 halph
  · exact query357 halph
  · exact query418 halph
  · exact query198 halph
  · exact query227 halph
  · exact query266 halph
  · exact query267 halph
  · exact query268 halph
  · exact query350 halph
  · exact query406 halph
  · exact query274 halph
  · exact query280 halph
  · exact query300 halph
  · exact query304 halph
  · exact query298 halph
  · exact query485 halph
  · exact query301 halph
  · exact query306 halph
  · exact query358 halph
  · exact query420 halph
  · exact query302 halph
  · exact query305 halph
  · exact query364 halph
  · exact query414 halph
  · exact query312 halph
  · exact query351 halph
  · exact query408 halph
  · exact query352 halph
  · exact query407 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link36 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link36 Q :=
  class_census link36 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source36
