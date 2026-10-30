import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source03
import C13Global.FastGroups.Source03Part00
import C13Global.FastGroups.Source03Part01
import C13Global.FastGroups.Source03Part02
namespace C13.Global.Relative.Source03
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source03
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link03 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link03 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link03 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link03 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_000.pointList FastDual03_000.columns FastDual03_000.rows FastDual03_000.bound (by decide +kernel)
    FastDual03_000.column_mask FastDual03_000.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,3,6,7} := rep000 halph

theorem rep001 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_001.pointList FastDual03_001.columns FastDual03_001.rows FastDual03_001.bound (by decide +kernel)
    FastDual03_001.column_mask FastDual03_001.checked hc F hF hroot hmin hout

theorem query299 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,3,6,8} := rep001 halph

def symmetry303 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query303 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,3,7,8} :=
  obstruction_transport link03 FastDual03_001.points {2,3,7,8} symmetry303
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry303 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry349 : Equiv.Perm Point where
  toFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  invFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query349 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,6,7,8} :=
  obstruction_transport link03 FastDual03_001.points {2,6,7,8} symmetry349
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry349 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry405 : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  invFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query405 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {3,6,7,8} :=
  obstruction_transport link03 FastDual03_001.points {3,6,7,8} symmetry405
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry405 (by decide +kernel)) (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_002.pointList FastDual03_002.columns FastDual03_002.rows FastDual03_002.bound (by decide +kernel)
    FastDual03_002.column_mask FastDual03_002.checked hc F hF hroot hmin hout

theorem query300 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,3,6,9} := rep002 halph

def symmetry304 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query304 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,3,7,9} :=
  obstruction_transport link03 FastDual03_002.points {2,3,7,9} symmetry304
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry304 (by decide +kernel)) (by decide +kernel) (rep002 halph)

def symmetry350 : Equiv.Perm Point where
  toFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  invFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query350 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,6,7,9} :=
  obstruction_transport link03 FastDual03_002.points {2,6,7,9} symmetry350
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry350 (by decide +kernel)) (by decide +kernel) (rep002 halph)

def symmetry406 : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  invFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query406 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {3,6,7,9} :=
  obstruction_transport link03 FastDual03_002.points {3,6,7,9} symmetry406
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry406 (by decide +kernel)) (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_003.pointList FastDual03_003.columns FastDual03_003.rows FastDual03_003.bound (by decide +kernel)
    FastDual03_003.column_mask FastDual03_003.checked hc F hF hroot hmin hout

theorem query301 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,3,6,10} := rep003 halph

def symmetry306 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query306 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,3,7,11} :=
  obstruction_transport link03 FastDual03_003.points {2,3,7,11} symmetry306
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry306 (by decide +kernel)) (by decide +kernel) (rep003 halph)

def symmetry351 : Equiv.Perm Point where
  toFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  invFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query351 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,6,7,10} :=
  obstruction_transport link03 FastDual03_003.points {2,6,7,10} symmetry351
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry351 (by decide +kernel)) (by decide +kernel) (rep003 halph)

def symmetry408 : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  invFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query408 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {3,6,7,11} :=
  obstruction_transport link03 FastDual03_003.points {3,6,7,11} symmetry408
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry408 (by decide +kernel)) (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_004.pointList FastDual03_004.columns FastDual03_004.rows FastDual03_004.bound (by decide +kernel)
    FastDual03_004.column_mask FastDual03_004.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,3,6,11} := rep004 halph

def symmetry305 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query305 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,3,7,10} :=
  obstruction_transport link03 FastDual03_004.points {2,3,7,10} symmetry305
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry305 (by decide +kernel)) (by decide +kernel) (rep004 halph)

def symmetry352 : Equiv.Perm Point where
  toFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  invFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query352 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,6,7,11} :=
  obstruction_transport link03 FastDual03_004.points {2,6,7,11} symmetry352
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry352 (by decide +kernel)) (by decide +kernel) (rep004 halph)

def symmetry407 : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  invFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query407 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {3,6,7,10} :=
  obstruction_transport link03 FastDual03_004.points {3,6,7,10} symmetry407
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry407 (by decide +kernel)) (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_005.pointList FastDual03_005.columns FastDual03_005.rows FastDual03_005.bound (by decide +kernel)
    FastDual03_005.column_mask FastDual03_005.checked hc F hF hroot hmin hout

theorem query307 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,3,8,9} := rep005 halph

def symmetry480 : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  invFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query480 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {6,7,8,9} :=
  obstruction_transport link03 FastDual03_005.points {6,7,8,9} symmetry480
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry480 (by decide +kernel)) (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_006.pointList FastDual03_006.columns FastDual03_006.rows FastDual03_006.bound (by decide +kernel)
    FastDual03_006.column_mask FastDual03_006.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,3,10,11} := rep006 halph

def symmetry485 : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  invFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query485 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {6,7,10,11} :=
  obstruction_transport link03 FastDual03_006.points {6,7,10,11} symmetry485
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry485 (by decide +kernel)) (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_007.pointList FastDual03_007.columns FastDual03_007.rows FastDual03_007.bound (by decide +kernel)
    FastDual03_007.column_mask FastDual03_007.checked hc F hF hroot hmin hout

theorem query353 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,6,8,9} := rep007 halph

def symmetry415 : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  invFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query415 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {3,7,8,9} :=
  obstruction_transport link03 FastDual03_007.points {3,7,8,9} symmetry415
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry415 (by decide +kernel)) (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_008.pointList FastDual03_008.columns FastDual03_008.rows FastDual03_008.bound (by decide +kernel)
    FastDual03_008.column_mask FastDual03_008.checked hc F hF hroot hmin hout

theorem query354 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,6,8,10} := rep008 halph

def symmetry417 : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  invFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query417 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {3,7,8,11} :=
  obstruction_transport link03 FastDual03_008.points {3,7,8,11} symmetry417
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry417 (by decide +kernel)) (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_009.pointList FastDual03_009.columns FastDual03_009.rows FastDual03_009.bound (by decide +kernel)
    FastDual03_009.column_mask FastDual03_009.checked hc F hF hroot hmin hout

theorem query355 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,6,8,11} := rep009 halph

def symmetry416 : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  invFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query416 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {3,7,8,10} :=
  obstruction_transport link03 FastDual03_009.points {3,7,8,10} symmetry416
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry416 (by decide +kernel)) (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_010.pointList FastDual03_010.columns FastDual03_010.rows FastDual03_010.bound (by decide +kernel)
    FastDual03_010.column_mask FastDual03_010.checked hc F hF hroot hmin hout

theorem query356 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,6,9,10} := rep010 halph

def symmetry419 : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  invFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query419 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {3,7,9,11} :=
  obstruction_transport link03 FastDual03_010.points {3,7,9,11} symmetry419
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry419 (by decide +kernel)) (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_011.pointList FastDual03_011.columns FastDual03_011.rows FastDual03_011.bound (by decide +kernel)
    FastDual03_011.column_mask FastDual03_011.checked hc F hF hroot hmin hout

theorem query357 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,6,9,11} := rep011 halph

def symmetry418 : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  invFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query418 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {3,7,9,10} :=
  obstruction_transport link03 FastDual03_011.points {3,7,9,10} symmetry418
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry418 (by decide +kernel)) (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_012.pointList FastDual03_012.columns FastDual03_012.rows FastDual03_012.bound (by decide +kernel)
    FastDual03_012.column_mask FastDual03_012.checked hc F hF hroot hmin hout

theorem query358 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,6,10,11} := rep012 halph

def symmetry420 : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  invFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query420 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {3,7,10,11} :=
  obstruction_transport link03 FastDual03_012.points {3,7,10,11} symmetry420
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry420 (by decide +kernel)) (by decide +kernel) (rep012 halph)

theorem rep013 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_013.pointList FastDual03_013.columns FastDual03_013.rows FastDual03_013.bound (by decide +kernel)
    FastDual03_013.column_mask FastDual03_013.checked hc F hF hroot hmin hout

theorem query359 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,7,8,9} := rep013 halph

def symmetry409 : Equiv.Perm Point where
  toFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  invFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query409 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {3,6,8,9} :=
  obstruction_transport link03 FastDual03_013.points {3,6,8,9} symmetry409
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry409 (by decide +kernel)) (by decide +kernel) (rep013 halph)

theorem rep014 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_014.pointList FastDual03_014.columns FastDual03_014.rows FastDual03_014.bound (by decide +kernel)
    FastDual03_014.column_mask FastDual03_014.checked hc F hF hroot hmin hout

theorem query360 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,7,8,10} := rep014 halph

def symmetry361 : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  invFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query361 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,7,8,11} :=
  obstruction_transport link03 FastDual03_014.points {2,7,8,11} symmetry361
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry361 (by decide +kernel)) (by decide +kernel) (rep014 halph)

def symmetry410 : Equiv.Perm Point where
  toFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  invFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query410 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {3,6,8,10} :=
  obstruction_transport link03 FastDual03_014.points {3,6,8,10} symmetry410
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry410 (by decide +kernel)) (by decide +kernel) (rep014 halph)

def symmetry411 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query411 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {3,6,8,11} :=
  obstruction_transport link03 FastDual03_014.points {3,6,8,11} symmetry411
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry411 (by decide +kernel)) (by decide +kernel) (rep014 halph)

theorem rep015 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_015.pointList FastDual03_015.columns FastDual03_015.rows FastDual03_015.bound (by decide +kernel)
    FastDual03_015.column_mask FastDual03_015.checked hc F hF hroot hmin hout

theorem query362 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,7,9,10} := rep015 halph

def symmetry363 : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  invFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query363 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,7,9,11} :=
  obstruction_transport link03 FastDual03_015.points {2,7,9,11} symmetry363
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry363 (by decide +kernel)) (by decide +kernel) (rep015 halph)

def symmetry412 : Equiv.Perm Point where
  toFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  invFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query412 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {3,6,9,10} :=
  obstruction_transport link03 FastDual03_015.points {3,6,9,10} symmetry412
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry412 (by decide +kernel)) (by decide +kernel) (rep015 halph)

def symmetry413 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query413 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {3,6,9,11} :=
  obstruction_transport link03 FastDual03_015.points {3,6,9,11} symmetry413
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry413 (by decide +kernel)) (by decide +kernel) (rep015 halph)

theorem rep016 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_016.pointList FastDual03_016.columns FastDual03_016.rows FastDual03_016.bound (by decide +kernel)
    FastDual03_016.column_mask FastDual03_016.checked hc F hF hroot hmin hout

theorem query364 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {2,7,10,11} := rep016 halph

def symmetry414 : Equiv.Perm Point where
  toFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  invFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query414 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {3,6,10,11} :=
  obstruction_transport link03 FastDual03_016.points {3,6,10,11} symmetry414
    (by decide +kernel) (root_symmetry_of_codes rootCodes link03 root_binding symmetry414 (by decide +kernel)) (by decide +kernel) (rep016 halph)

theorem rep017 (halph : AlphabetComplete link03 alphabets) :
    ActualObstruction link03 FastDual03_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link03 rootCodes root_binding alphabets halph nonincident_complete
    FastDual03_017.pointList FastDual03_017.columns FastDual03_017.rows FastDual03_017.bound (by decide +kernel)
    FastDual03_017.column_mask FastDual03_017.checked hc F hF hroot hmin hout

theorem query494 (halph : AlphabetComplete link03 alphabets) : ActualObstruction link03 {8,9,10,11} := rep017 halph

def dualQuads : List (Finset Point) := [{2,3,6,7},{2,3,6,8},{2,3,7,8},{2,6,7,8},{3,6,7,8},{2,3,6,9},{2,3,7,9},{2,6,7,9},{3,6,7,9},{2,3,6,10},{2,3,7,11},{2,6,7,10},{3,6,7,11},{2,3,6,11},{2,3,7,10},{2,6,7,11},{3,6,7,10},{2,3,8,9},{6,7,8,9},{2,3,10,11},{6,7,10,11},{2,6,8,9},{3,7,8,9},{2,6,8,10},{3,7,8,11},{2,6,8,11},{3,7,8,10},{2,6,9,10},{3,7,9,11},{2,6,9,11},{3,7,9,10},{2,6,10,11},{3,7,10,11},{2,7,8,9},{3,6,8,9},{2,7,8,10},{2,7,8,11},{3,6,8,10},{3,6,8,11},{2,7,9,10},{2,7,9,11},{3,6,9,10},{3,6,9,11},{2,7,10,11},{3,6,10,11},{8,9,10,11}]

theorem dual_actual (halph : AlphabetComplete link03 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link03 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query298 halph
  · exact query299 halph
  · exact query303 halph
  · exact query349 halph
  · exact query405 halph
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
  · exact query307 halph
  · exact query480 halph
  · exact query312 halph
  · exact query485 halph
  · exact query353 halph
  · exact query415 halph
  · exact query354 halph
  · exact query417 halph
  · exact query355 halph
  · exact query416 halph
  · exact query356 halph
  · exact query419 halph
  · exact query357 halph
  · exact query418 halph
  · exact query358 halph
  · exact query420 halph
  · exact query359 halph
  · exact query409 halph
  · exact query360 halph
  · exact query361 halph
  · exact query410 halph
  · exact query411 halph
  · exact query362 halph
  · exact query363 halph
  · exact query412 halph
  · exact query413 halph
  · exact query364 halph
  · exact query414 halph
  · exact query494 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link03 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link03 Q :=
  class_census link03 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source03
