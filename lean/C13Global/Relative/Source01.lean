import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source01
import C13Global.FastGroups.Source01Part00
import C13Global.FastGroups.Source01Part01
namespace C13.Global.Relative.Source01
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source01
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link01 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link01 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link01 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link01 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link01 alphabets) :
    ActualObstruction link01 FastDual01_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link01 rootCodes root_binding alphabets halph nonincident_complete
    FastDual01_000.pointList FastDual01_000.columns FastDual01_000.rows FastDual01_000.bound (by decide +kernel)
    FastDual01_000.column_mask FastDual01_000.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,3,6,7} := rep000 halph

theorem rep001 (halph : AlphabetComplete link01 alphabets) :
    ActualObstruction link01 FastDual01_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link01 rootCodes root_binding alphabets halph nonincident_complete
    FastDual01_001.pointList FastDual01_001.columns FastDual01_001.rows FastDual01_001.bound (by decide +kernel)
    FastDual01_001.column_mask FastDual01_001.checked hc F hF hroot hmin hout

theorem query299 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,3,6,8} := rep001 halph

def symmetry300 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query300 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,3,6,9} :=
  obstruction_transport link01 FastDual01_001.points {2,3,6,9} symmetry300
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry300 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry303 : Equiv.Perm Point where
  toFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  invFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query303 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,3,7,8} :=
  obstruction_transport link01 FastDual01_001.points {2,3,7,8} symmetry303
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry303 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry304 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query304 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,3,7,9} :=
  obstruction_transport link01 FastDual01_001.points {2,3,7,9} symmetry304
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry304 (by decide +kernel)) (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link01 alphabets) :
    ActualObstruction link01 FastDual01_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link01 rootCodes root_binding alphabets halph nonincident_complete
    FastDual01_002.pointList FastDual01_002.columns FastDual01_002.rows FastDual01_002.bound (by decide +kernel)
    FastDual01_002.column_mask FastDual01_002.checked hc F hF hroot hmin hout

theorem query301 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,3,6,10} := rep002 halph

def symmetry302 : Equiv.Perm Point where
  toFun := ![1,0,2,3,5,4,6,7,8,9,11,10,12]
  invFun := ![1,0,2,3,5,4,6,7,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query302 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,3,6,11} :=
  obstruction_transport link01 FastDual01_002.points {2,3,6,11} symmetry302
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry302 (by decide +kernel)) (by decide +kernel) (rep002 halph)

def symmetry305 : Equiv.Perm Point where
  toFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  invFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query305 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,3,7,10} :=
  obstruction_transport link01 FastDual01_002.points {2,3,7,10} symmetry305
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry305 (by decide +kernel)) (by decide +kernel) (rep002 halph)

def symmetry306 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query306 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,3,7,11} :=
  obstruction_transport link01 FastDual01_002.points {2,3,7,11} symmetry306
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry306 (by decide +kernel)) (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link01 alphabets) :
    ActualObstruction link01 FastDual01_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link01 rootCodes root_binding alphabets halph nonincident_complete
    FastDual01_003.pointList FastDual01_003.columns FastDual01_003.rows FastDual01_003.bound (by decide +kernel)
    FastDual01_003.column_mask FastDual01_003.checked hc F hF hroot hmin hout

theorem query307 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,3,8,9} := rep003 halph

theorem rep004 (halph : AlphabetComplete link01 alphabets) :
    ActualObstruction link01 FastDual01_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link01 rootCodes root_binding alphabets halph nonincident_complete
    FastDual01_004.pointList FastDual01_004.columns FastDual01_004.rows FastDual01_004.bound (by decide +kernel)
    FastDual01_004.column_mask FastDual01_004.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,3,10,11} := rep004 halph

theorem rep005 (halph : AlphabetComplete link01 alphabets) :
    ActualObstruction link01 FastDual01_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link01 rootCodes root_binding alphabets halph nonincident_complete
    FastDual01_005.pointList FastDual01_005.columns FastDual01_005.rows FastDual01_005.bound (by decide +kernel)
    FastDual01_005.column_mask FastDual01_005.checked hc F hF hroot hmin hout

theorem query349 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,6,7,8} := rep005 halph

def symmetry350 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query350 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,6,7,9} :=
  obstruction_transport link01 FastDual01_005.points {2,6,7,9} symmetry350
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry350 (by decide +kernel)) (by decide +kernel) (rep005 halph)

def symmetry405 : Equiv.Perm Point where
  toFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  invFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query405 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {3,6,7,8} :=
  obstruction_transport link01 FastDual01_005.points {3,6,7,8} symmetry405
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry405 (by decide +kernel)) (by decide +kernel) (rep005 halph)

def symmetry406 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query406 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {3,6,7,9} :=
  obstruction_transport link01 FastDual01_005.points {3,6,7,9} symmetry406
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry406 (by decide +kernel)) (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link01 alphabets) :
    ActualObstruction link01 FastDual01_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link01 rootCodes root_binding alphabets halph nonincident_complete
    FastDual01_006.pointList FastDual01_006.columns FastDual01_006.rows FastDual01_006.bound (by decide +kernel)
    FastDual01_006.column_mask FastDual01_006.checked hc F hF hroot hmin hout

theorem query351 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,6,7,10} := rep006 halph

def symmetry352 : Equiv.Perm Point where
  toFun := ![1,0,2,3,5,4,6,7,8,9,11,10,12]
  invFun := ![1,0,2,3,5,4,6,7,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query352 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,6,7,11} :=
  obstruction_transport link01 FastDual01_006.points {2,6,7,11} symmetry352
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry352 (by decide +kernel)) (by decide +kernel) (rep006 halph)

def symmetry407 : Equiv.Perm Point where
  toFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  invFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query407 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {3,6,7,10} :=
  obstruction_transport link01 FastDual01_006.points {3,6,7,10} symmetry407
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry407 (by decide +kernel)) (by decide +kernel) (rep006 halph)

def symmetry408 : Equiv.Perm Point where
  toFun := ![1,0,3,2,4,5,6,7,9,8,11,10,12]
  invFun := ![1,0,3,2,4,5,6,7,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query408 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {3,6,7,11} :=
  obstruction_transport link01 FastDual01_006.points {3,6,7,11} symmetry408
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry408 (by decide +kernel)) (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link01 alphabets) :
    ActualObstruction link01 FastDual01_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link01 rootCodes root_binding alphabets halph nonincident_complete
    FastDual01_007.pointList FastDual01_007.columns FastDual01_007.rows FastDual01_007.bound (by decide +kernel)
    FastDual01_007.column_mask FastDual01_007.checked hc F hF hroot hmin hout

theorem query353 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,6,8,9} := rep007 halph

def symmetry359 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query359 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,7,8,9} :=
  obstruction_transport link01 FastDual01_007.points {2,7,8,9} symmetry359
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry359 (by decide +kernel)) (by decide +kernel) (rep007 halph)

def symmetry409 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query409 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {3,6,8,9} :=
  obstruction_transport link01 FastDual01_007.points {3,6,8,9} symmetry409
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry409 (by decide +kernel)) (by decide +kernel) (rep007 halph)

def symmetry415 : Equiv.Perm Point where
  toFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  invFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query415 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {3,7,8,9} :=
  obstruction_transport link01 FastDual01_007.points {3,7,8,9} symmetry415
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry415 (by decide +kernel)) (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link01 alphabets) :
    ActualObstruction link01 FastDual01_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link01 rootCodes root_binding alphabets halph nonincident_complete
    FastDual01_008.pointList FastDual01_008.columns FastDual01_008.rows FastDual01_008.bound (by decide +kernel)
    FastDual01_008.column_mask FastDual01_008.checked hc F hF hroot hmin hout

theorem query354 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,6,8,10} := rep008 halph

def symmetry355 : Equiv.Perm Point where
  toFun := ![1,0,2,3,5,4,6,7,8,9,11,10,12]
  invFun := ![1,0,2,3,5,4,6,7,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query355 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,6,8,11} :=
  obstruction_transport link01 FastDual01_008.points {2,6,8,11} symmetry355
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry355 (by decide +kernel)) (by decide +kernel) (rep008 halph)

def symmetry362 : Equiv.Perm Point where
  toFun := ![1,0,2,3,4,5,7,6,9,8,10,11,12]
  invFun := ![1,0,2,3,4,5,7,6,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query362 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,7,9,10} :=
  obstruction_transport link01 FastDual01_008.points {2,7,9,10} symmetry362
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry362 (by decide +kernel)) (by decide +kernel) (rep008 halph)

def symmetry363 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query363 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,7,9,11} :=
  obstruction_transport link01 FastDual01_008.points {2,7,9,11} symmetry363
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry363 (by decide +kernel)) (by decide +kernel) (rep008 halph)

def symmetry412 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query412 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {3,6,9,10} :=
  obstruction_transport link01 FastDual01_008.points {3,6,9,10} symmetry412
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry412 (by decide +kernel)) (by decide +kernel) (rep008 halph)

def symmetry413 : Equiv.Perm Point where
  toFun := ![1,0,3,2,4,5,6,7,9,8,11,10,12]
  invFun := ![1,0,3,2,4,5,6,7,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query413 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {3,6,9,11} :=
  obstruction_transport link01 FastDual01_008.points {3,6,9,11} symmetry413
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry413 (by decide +kernel)) (by decide +kernel) (rep008 halph)

def symmetry416 : Equiv.Perm Point where
  toFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  invFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query416 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {3,7,8,10} :=
  obstruction_transport link01 FastDual01_008.points {3,7,8,10} symmetry416
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry416 (by decide +kernel)) (by decide +kernel) (rep008 halph)

def symmetry417 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query417 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {3,7,8,11} :=
  obstruction_transport link01 FastDual01_008.points {3,7,8,11} symmetry417
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry417 (by decide +kernel)) (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link01 alphabets) :
    ActualObstruction link01 FastDual01_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link01 rootCodes root_binding alphabets halph nonincident_complete
    FastDual01_009.pointList FastDual01_009.columns FastDual01_009.rows FastDual01_009.bound (by decide +kernel)
    FastDual01_009.column_mask FastDual01_009.checked hc F hF hroot hmin hout

theorem query356 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,6,9,10} := rep009 halph

def symmetry357 : Equiv.Perm Point where
  toFun := ![1,0,2,3,5,4,6,7,8,9,11,10,12]
  invFun := ![1,0,2,3,5,4,6,7,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query357 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,6,9,11} :=
  obstruction_transport link01 FastDual01_009.points {2,6,9,11} symmetry357
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry357 (by decide +kernel)) (by decide +kernel) (rep009 halph)

def symmetry360 : Equiv.Perm Point where
  toFun := ![1,0,2,3,4,5,7,6,9,8,10,11,12]
  invFun := ![1,0,2,3,4,5,7,6,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query360 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,7,8,10} :=
  obstruction_transport link01 FastDual01_009.points {2,7,8,10} symmetry360
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry360 (by decide +kernel)) (by decide +kernel) (rep009 halph)

def symmetry361 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query361 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,7,8,11} :=
  obstruction_transport link01 FastDual01_009.points {2,7,8,11} symmetry361
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry361 (by decide +kernel)) (by decide +kernel) (rep009 halph)

def symmetry410 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query410 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {3,6,8,10} :=
  obstruction_transport link01 FastDual01_009.points {3,6,8,10} symmetry410
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry410 (by decide +kernel)) (by decide +kernel) (rep009 halph)

def symmetry411 : Equiv.Perm Point where
  toFun := ![1,0,3,2,4,5,6,7,9,8,11,10,12]
  invFun := ![1,0,3,2,4,5,6,7,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query411 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {3,6,8,11} :=
  obstruction_transport link01 FastDual01_009.points {3,6,8,11} symmetry411
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry411 (by decide +kernel)) (by decide +kernel) (rep009 halph)

def symmetry418 : Equiv.Perm Point where
  toFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  invFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query418 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {3,7,9,10} :=
  obstruction_transport link01 FastDual01_009.points {3,7,9,10} symmetry418
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry418 (by decide +kernel)) (by decide +kernel) (rep009 halph)

def symmetry419 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query419 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {3,7,9,11} :=
  obstruction_transport link01 FastDual01_009.points {3,7,9,11} symmetry419
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry419 (by decide +kernel)) (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link01 alphabets) :
    ActualObstruction link01 FastDual01_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link01 rootCodes root_binding alphabets halph nonincident_complete
    FastDual01_010.pointList FastDual01_010.columns FastDual01_010.rows FastDual01_010.bound (by decide +kernel)
    FastDual01_010.column_mask FastDual01_010.checked hc F hF hroot hmin hout

theorem query358 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,6,10,11} := rep010 halph

def symmetry364 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query364 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {2,7,10,11} :=
  obstruction_transport link01 FastDual01_010.points {2,7,10,11} symmetry364
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry364 (by decide +kernel)) (by decide +kernel) (rep010 halph)

def symmetry414 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query414 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {3,6,10,11} :=
  obstruction_transport link01 FastDual01_010.points {3,6,10,11} symmetry414
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry414 (by decide +kernel)) (by decide +kernel) (rep010 halph)

def symmetry420 : Equiv.Perm Point where
  toFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  invFun := ![1,0,3,2,5,4,7,6,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query420 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {3,7,10,11} :=
  obstruction_transport link01 FastDual01_010.points {3,7,10,11} symmetry420
    (by decide +kernel) (root_symmetry_of_codes rootCodes link01 root_binding symmetry420 (by decide +kernel)) (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link01 alphabets) :
    ActualObstruction link01 FastDual01_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link01 rootCodes root_binding alphabets halph nonincident_complete
    FastDual01_011.pointList FastDual01_011.columns FastDual01_011.rows FastDual01_011.bound (by decide +kernel)
    FastDual01_011.column_mask FastDual01_011.checked hc F hF hroot hmin hout

theorem query480 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {6,7,8,9} := rep011 halph

theorem rep012 (halph : AlphabetComplete link01 alphabets) :
    ActualObstruction link01 FastDual01_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link01 rootCodes root_binding alphabets halph nonincident_complete
    FastDual01_012.pointList FastDual01_012.columns FastDual01_012.rows FastDual01_012.bound (by decide +kernel)
    FastDual01_012.column_mask FastDual01_012.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {6,7,10,11} := rep012 halph

theorem rep013 (halph : AlphabetComplete link01 alphabets) :
    ActualObstruction link01 FastDual01_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link01 rootCodes root_binding alphabets halph nonincident_complete
    FastDual01_013.pointList FastDual01_013.columns FastDual01_013.rows FastDual01_013.bound (by decide +kernel)
    FastDual01_013.column_mask FastDual01_013.checked hc F hF hroot hmin hout

theorem query494 (halph : AlphabetComplete link01 alphabets) : ActualObstruction link01 {8,9,10,11} := rep013 halph

def dualQuads : List (Finset Point) := [{2,3,6,7},{2,3,6,8},{2,3,6,9},{2,3,7,8},{2,3,7,9},{2,3,6,10},{2,3,6,11},{2,3,7,10},{2,3,7,11},{2,3,8,9},{2,3,10,11},{2,6,7,8},{2,6,7,9},{3,6,7,8},{3,6,7,9},{2,6,7,10},{2,6,7,11},{3,6,7,10},{3,6,7,11},{2,6,8,9},{2,7,8,9},{3,6,8,9},{3,7,8,9},{2,6,8,10},{2,6,8,11},{2,7,9,10},{2,7,9,11},{3,6,9,10},{3,6,9,11},{3,7,8,10},{3,7,8,11},{2,6,9,10},{2,6,9,11},{2,7,8,10},{2,7,8,11},{3,6,8,10},{3,6,8,11},{3,7,9,10},{3,7,9,11},{2,6,10,11},{2,7,10,11},{3,6,10,11},{3,7,10,11},{6,7,8,9},{6,7,10,11},{8,9,10,11}]

theorem dual_actual (halph : AlphabetComplete link01 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link01 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query298 halph
  · exact query299 halph
  · exact query300 halph
  · exact query303 halph
  · exact query304 halph
  · exact query301 halph
  · exact query302 halph
  · exact query305 halph
  · exact query306 halph
  · exact query307 halph
  · exact query312 halph
  · exact query349 halph
  · exact query350 halph
  · exact query405 halph
  · exact query406 halph
  · exact query351 halph
  · exact query352 halph
  · exact query407 halph
  · exact query408 halph
  · exact query353 halph
  · exact query359 halph
  · exact query409 halph
  · exact query415 halph
  · exact query354 halph
  · exact query355 halph
  · exact query362 halph
  · exact query363 halph
  · exact query412 halph
  · exact query413 halph
  · exact query416 halph
  · exact query417 halph
  · exact query356 halph
  · exact query357 halph
  · exact query360 halph
  · exact query361 halph
  · exact query410 halph
  · exact query411 halph
  · exact query418 halph
  · exact query419 halph
  · exact query358 halph
  · exact query364 halph
  · exact query414 halph
  · exact query420 halph
  · exact query480 halph
  · exact query485 halph
  · exact query494 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link01 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link01 Q :=
  class_census link01 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source01
