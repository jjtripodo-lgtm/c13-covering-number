import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source50
import C13Global.FastGroups.Source50Part00
import C13Global.FastGroups.Source50Part01
import C13Global.FastGroups.Source50Part02
namespace C13.Global.Relative.Source50
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source50
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link50 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link50 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link50 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link50 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_000.pointList FastDual50_000.columns FastDual50_000.rows FastDual50_000.bound (by decide +kernel)
    FastDual50_000.column_mask FastDual50_000.checked hc F hF hroot hmin hout

theorem query167 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,2,3,6} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![10,11,9,8,5,4,6,7,3,2,0,1,12]
  invFun := ![10,11,9,8,5,4,6,7,3,2,0,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link50 = link50 :=
  root_symmetry_of_codes rootCodes link50 root_binding automorphism000 (by decide +kernel)

theorem query487 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {6,8,9,11} :=
  obstruction_transport link50 FastDual50_000.points {6,8,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_001.pointList FastDual50_001.columns FastDual50_001.rows FastDual50_001.bound (by decide +kernel)
    FastDual50_001.column_mask FastDual50_001.checked hc F hF hroot hmin hout

theorem query187 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,2,6,8} := rep001 halph

def automorphism001 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism001_hole : automorphism001 hole = hole := by decide +kernel

theorem automorphism001_root : transport automorphism001 link50 = link50 :=
  root_symmetry_of_codes rootCodes link50 root_binding automorphism001 (by decide +kernel)

theorem query216 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,3,6,9} :=
  obstruction_transport link50 FastDual50_001.points {1,3,6,9} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep001 halph)

def automorphism002 : Equiv.Perm Point where
  toFun := ![10,11,8,9,4,5,6,7,2,3,0,1,12]
  invFun := ![10,11,8,9,4,5,6,7,2,3,0,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism002_hole : automorphism002 hole = hole := by decide +kernel

theorem automorphism002_root : transport automorphism002 link50 = link50 :=
  root_symmetry_of_codes rootCodes link50 root_binding automorphism002 (by decide +kernel)

theorem query355 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,6,8,11} :=
  obstruction_transport link50 FastDual50_001.points {2,6,8,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep001 halph)

theorem query413 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {3,6,9,11} :=
  obstruction_transport link50 FastDual50_001.points {3,6,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_002.pointList FastDual50_002.columns FastDual50_002.rows FastDual50_002.bound (by decide +kernel)
    FastDual50_002.column_mask FastDual50_002.checked hc F hF hroot hmin hout

theorem query188 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,2,6,9} := rep002 halph

theorem query215 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,3,6,8} :=
  obstruction_transport link50 FastDual50_002.points {1,3,6,8} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep002 halph)

theorem query357 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,6,9,11} :=
  obstruction_transport link50 FastDual50_002.points {2,6,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem query411 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {3,6,8,11} :=
  obstruction_transport link50 FastDual50_002.points {3,6,8,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_003.pointList FastDual50_003.columns FastDual50_003.rows FastDual50_003.bound (by decide +kernel)
    FastDual50_003.column_mask FastDual50_003.checked hc F hF hroot hmin hout

theorem query190 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,2,6,11} := rep003 halph

theorem query218 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,3,6,11} :=
  obstruction_transport link50 FastDual50_003.points {1,3,6,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep003 halph)

theorem query271 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,6,8,11} :=
  obstruction_transport link50 FastDual50_003.points {1,6,8,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep003 halph)

theorem query273 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,6,9,11} :=
  obstruction_transport link50 FastDual50_003.points {1,6,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_004.pointList FastDual50_004.columns FastDual50_004.rows FastDual50_004.bound (by decide +kernel)
    FastDual50_004.column_mask FastDual50_004.checked hc F hF hroot hmin hout

theorem query191 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,2,7,8} := rep004 halph

theorem query220 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,3,7,9} :=
  obstruction_transport link50 FastDual50_004.points {1,3,7,9} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep004 halph)

theorem query361 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,7,8,11} :=
  obstruction_transport link50 FastDual50_004.points {2,7,8,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep004 halph)

theorem query419 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {3,7,9,11} :=
  obstruction_transport link50 FastDual50_004.points {3,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_005.pointList FastDual50_005.columns FastDual50_005.rows FastDual50_005.bound (by decide +kernel)
    FastDual50_005.column_mask FastDual50_005.checked hc F hF hroot hmin hout

theorem query192 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,2,7,9} := rep005 halph

theorem query219 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,3,7,8} :=
  obstruction_transport link50 FastDual50_005.points {1,3,7,8} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep005 halph)

theorem query363 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,7,9,11} :=
  obstruction_transport link50 FastDual50_005.points {2,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem query417 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {3,7,8,11} :=
  obstruction_transport link50 FastDual50_005.points {3,7,8,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_006.pointList FastDual50_006.columns FastDual50_006.rows FastDual50_006.bound (by decide +kernel)
    FastDual50_006.column_mask FastDual50_006.checked hc F hF hroot hmin hout

theorem query194 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,2,7,11} := rep006 halph

theorem query222 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,3,7,11} :=
  obstruction_transport link50 FastDual50_006.points {1,3,7,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep006 halph)

theorem query277 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,7,8,11} :=
  obstruction_transport link50 FastDual50_006.points {1,7,8,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep006 halph)

theorem query279 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,7,9,11} :=
  obstruction_transport link50 FastDual50_006.points {1,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_007.pointList FastDual50_007.columns FastDual50_007.rows FastDual50_007.bound (by decide +kernel)
    FastDual50_007.column_mask FastDual50_007.checked hc F hF hroot hmin hout

theorem query197 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,2,8,11} := rep007 halph

theorem query227 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,3,9,11} :=
  obstruction_transport link50 FastDual50_007.points {1,3,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_008.pointList FastDual50_008.columns FastDual50_008.rows FastDual50_008.bound (by decide +kernel)
    FastDual50_008.column_mask FastDual50_008.checked hc F hF hroot hmin hout

theorem query265 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,6,7,8} := rep008 halph

theorem query266 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,6,7,9} :=
  obstruction_transport link50 FastDual50_008.points {1,6,7,9} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep008 halph)

theorem query352 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,6,7,11} :=
  obstruction_transport link50 FastDual50_008.points {2,6,7,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep008 halph)

theorem query408 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {3,6,7,11} :=
  obstruction_transport link50 FastDual50_008.points {3,6,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_009.pointList FastDual50_009.columns FastDual50_009.rows FastDual50_009.bound (by decide +kernel)
    FastDual50_009.column_mask FastDual50_009.checked hc F hF hroot hmin hout

theorem query268 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,6,7,11} := rep009 halph

theorem rep010 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_010.pointList FastDual50_010.columns FastDual50_010.rows FastDual50_010.bound (by decide +kernel)
    FastDual50_010.column_mask FastDual50_010.checked hc F hF hroot hmin hout

theorem query269 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,6,8,9} := rep010 halph

theorem query302 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,3,6,11} :=
  obstruction_transport link50 FastDual50_010.points {2,3,6,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_011.pointList FastDual50_011.columns FastDual50_011.rows FastDual50_011.bound (by decide +kernel)
    FastDual50_011.column_mask FastDual50_011.checked hc F hF hroot hmin hout

theorem query275 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {1,7,8,9} := rep011 halph

theorem query306 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,3,7,11} :=
  obstruction_transport link50 FastDual50_011.points {2,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_012.pointList FastDual50_012.columns FastDual50_012.rows FastDual50_012.bound (by decide +kernel)
    FastDual50_012.column_mask FastDual50_012.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,3,6,7} := rep012 halph

theorem query480 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {6,7,8,9} :=
  obstruction_transport link50 FastDual50_012.points {6,7,8,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep012 halph)

theorem rep013 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_013.pointList FastDual50_013.columns FastDual50_013.rows FastDual50_013.bound (by decide +kernel)
    FastDual50_013.column_mask FastDual50_013.checked hc F hF hroot hmin hout

theorem query299 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,3,6,8} := rep013 halph

theorem query300 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,3,6,9} :=
  obstruction_transport link50 FastDual50_013.points {2,3,6,9} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep013 halph)

theorem query353 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,6,8,9} :=
  obstruction_transport link50 FastDual50_013.points {2,6,8,9} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep013 halph)

theorem query409 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {3,6,8,9} :=
  obstruction_transport link50 FastDual50_013.points {3,6,8,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep013 halph)

theorem rep014 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_014.pointList FastDual50_014.columns FastDual50_014.rows FastDual50_014.bound (by decide +kernel)
    FastDual50_014.column_mask FastDual50_014.checked hc F hF hroot hmin hout

theorem query303 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,3,7,8} := rep014 halph

theorem query304 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,3,7,9} :=
  obstruction_transport link50 FastDual50_014.points {2,3,7,9} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep014 halph)

theorem query359 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,7,8,9} :=
  obstruction_transport link50 FastDual50_014.points {2,7,8,9} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep014 halph)

theorem query415 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {3,7,8,9} :=
  obstruction_transport link50 FastDual50_014.points {3,7,8,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep014 halph)

theorem rep015 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_015.pointList FastDual50_015.columns FastDual50_015.rows FastDual50_015.bound (by decide +kernel)
    FastDual50_015.column_mask FastDual50_015.checked hc F hF hroot hmin hout

theorem query307 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,3,8,9} := rep015 halph

theorem rep016 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_016.pointList FastDual50_016.columns FastDual50_016.rows FastDual50_016.bound (by decide +kernel)
    FastDual50_016.column_mask FastDual50_016.checked hc F hF hroot hmin hout

theorem query349 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,6,7,8} := rep016 halph

theorem query406 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {3,6,7,9} :=
  obstruction_transport link50 FastDual50_016.points {3,6,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep016 halph)

theorem rep017 (halph : AlphabetComplete link50 alphabets) :
    ActualObstruction link50 FastDual50_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link50 rootCodes root_binding alphabets halph nonincident_complete
    FastDual50_017.pointList FastDual50_017.columns FastDual50_017.rows FastDual50_017.bound (by decide +kernel)
    FastDual50_017.column_mask FastDual50_017.checked hc F hF hroot hmin hout

theorem query350 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {2,6,7,9} := rep017 halph

theorem query405 (halph : AlphabetComplete link50 alphabets) : ActualObstruction link50 {3,6,7,8} :=
  obstruction_transport link50 FastDual50_017.points {3,6,7,8} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep017 halph)

def dualQuads : List (Finset Point) := [{1,2,3,6},{6,8,9,11},{1,2,6,8},{1,3,6,9},{2,6,8,11},{3,6,9,11},{1,2,6,9},{1,3,6,8},{2,6,9,11},{3,6,8,11},{1,2,6,11},{1,3,6,11},{1,6,8,11},{1,6,9,11},{1,2,7,8},{1,3,7,9},{2,7,8,11},{3,7,9,11},{1,2,7,9},{1,3,7,8},{2,7,9,11},{3,7,8,11},{1,2,7,11},{1,3,7,11},{1,7,8,11},{1,7,9,11},{1,2,8,11},{1,3,9,11},{1,6,7,8},{1,6,7,9},{2,6,7,11},{3,6,7,11},{1,6,7,11},{1,6,8,9},{2,3,6,11},{1,7,8,9},{2,3,7,11},{2,3,6,7},{6,7,8,9},{2,3,6,8},{2,3,6,9},{2,6,8,9},{3,6,8,9},{2,3,7,8},{2,3,7,9},{2,7,8,9},{3,7,8,9},{2,3,8,9},{2,6,7,8},{3,6,7,9},{2,6,7,9},{3,6,7,8}]

theorem dual_actual (halph : AlphabetComplete link50 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link50 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query167 halph
  · exact query487 halph
  · exact query187 halph
  · exact query216 halph
  · exact query355 halph
  · exact query413 halph
  · exact query188 halph
  · exact query215 halph
  · exact query357 halph
  · exact query411 halph
  · exact query190 halph
  · exact query218 halph
  · exact query271 halph
  · exact query273 halph
  · exact query191 halph
  · exact query220 halph
  · exact query361 halph
  · exact query419 halph
  · exact query192 halph
  · exact query219 halph
  · exact query363 halph
  · exact query417 halph
  · exact query194 halph
  · exact query222 halph
  · exact query277 halph
  · exact query279 halph
  · exact query197 halph
  · exact query227 halph
  · exact query265 halph
  · exact query266 halph
  · exact query352 halph
  · exact query408 halph
  · exact query268 halph
  · exact query269 halph
  · exact query302 halph
  · exact query275 halph
  · exact query306 halph
  · exact query298 halph
  · exact query480 halph
  · exact query299 halph
  · exact query300 halph
  · exact query353 halph
  · exact query409 halph
  · exact query303 halph
  · exact query304 halph
  · exact query359 halph
  · exact query415 halph
  · exact query307 halph
  · exact query349 halph
  · exact query406 halph
  · exact query350 halph
  · exact query405 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link50 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link50 Q :=
  class_census link50 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source50
