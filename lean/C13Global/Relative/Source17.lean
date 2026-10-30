import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source17
import C13Global.FastGroups.Source17Part00
import C13Global.FastGroups.Source17Part01
import C13Global.FastGroups.Source17Part02
import C13Global.FastGroups.Source17Part03
namespace C13.Global.Relative.Source17
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source17
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link17 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link17 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link17 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link17 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_000.pointList FastDual17_000.columns FastDual17_000.rows FastDual17_000.bound (by decide +kernel)
    FastDual17_000.column_mask FastDual17_000.checked hc F hF hroot hmin hout

theorem query215 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,3,6,8} := rep000 halph

def symmetry265 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query265 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,6,7,8} :=
  obstruction_transport link17 FastDual17_000.points {1,6,7,8} symmetry265
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry265 (by decide +kernel)) (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_001.pointList FastDual17_001.columns FastDual17_001.rows FastDual17_001.bound (by decide +kernel)
    FastDual17_001.column_mask FastDual17_001.checked hc F hF hroot hmin hout

theorem query216 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,3,6,9} := rep001 halph

def symmetry267 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query267 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,6,7,10} :=
  obstruction_transport link17 FastDual17_001.points {1,6,7,10} symmetry267
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry267 (by decide +kernel)) (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_002.pointList FastDual17_002.columns FastDual17_002.rows FastDual17_002.bound (by decide +kernel)
    FastDual17_002.column_mask FastDual17_002.checked hc F hF hroot hmin hout

theorem query217 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,3,6,10} := rep002 halph

def symmetry266 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query266 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,6,7,9} :=
  obstruction_transport link17 FastDual17_002.points {1,6,7,9} symmetry266
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry266 (by decide +kernel)) (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_003.pointList FastDual17_003.columns FastDual17_003.rows FastDual17_003.bound (by decide +kernel)
    FastDual17_003.column_mask FastDual17_003.checked hc F hF hroot hmin hout

theorem query218 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,3,6,11} := rep003 halph

def symmetry268 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query268 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,6,7,11} :=
  obstruction_transport link17 FastDual17_003.points {1,6,7,11} symmetry268
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry268 (by decide +kernel)) (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_004.pointList FastDual17_004.columns FastDual17_004.rows FastDual17_004.bound (by decide +kernel)
    FastDual17_004.column_mask FastDual17_004.checked hc F hF hroot hmin hout

theorem query219 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,3,7,8} := rep004 halph

def symmetry405 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query405 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {3,6,7,8} :=
  obstruction_transport link17 FastDual17_004.points {3,6,7,8} symmetry405
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry405 (by decide +kernel)) (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_005.pointList FastDual17_005.columns FastDual17_005.rows FastDual17_005.bound (by decide +kernel)
    FastDual17_005.column_mask FastDual17_005.checked hc F hF hroot hmin hout

theorem query220 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,3,7,9} := rep005 halph

def symmetry407 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query407 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {3,6,7,10} :=
  obstruction_transport link17 FastDual17_005.points {3,6,7,10} symmetry407
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry407 (by decide +kernel)) (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_006.pointList FastDual17_006.columns FastDual17_006.rows FastDual17_006.bound (by decide +kernel)
    FastDual17_006.column_mask FastDual17_006.checked hc F hF hroot hmin hout

theorem query221 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,3,7,10} := rep006 halph

def symmetry406 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query406 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {3,6,7,9} :=
  obstruction_transport link17 FastDual17_006.points {3,6,7,9} symmetry406
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry406 (by decide +kernel)) (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_007.pointList FastDual17_007.columns FastDual17_007.rows FastDual17_007.bound (by decide +kernel)
    FastDual17_007.column_mask FastDual17_007.checked hc F hF hroot hmin hout

theorem query222 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,3,7,11} := rep007 halph

def symmetry408 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query408 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {3,6,7,11} :=
  obstruction_transport link17 FastDual17_007.points {3,6,7,11} symmetry408
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry408 (by decide +kernel)) (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_008.pointList FastDual17_008.columns FastDual17_008.rows FastDual17_008.bound (by decide +kernel)
    FastDual17_008.column_mask FastDual17_008.checked hc F hF hroot hmin hout

theorem query224 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,3,8,10} := rep008 halph

def symmetry480 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query480 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {6,7,8,9} :=
  obstruction_transport link17 FastDual17_008.points {6,7,8,9} symmetry480
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry480 (by decide +kernel)) (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_009.pointList FastDual17_009.columns FastDual17_009.rows FastDual17_009.bound (by decide +kernel)
    FastDual17_009.column_mask FastDual17_009.checked hc F hF hroot hmin hout

theorem query227 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,3,9,11} := rep009 halph

def symmetry485 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query485 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {6,7,10,11} :=
  obstruction_transport link17 FastDual17_009.points {6,7,10,11} symmetry485
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry485 (by decide +kernel)) (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_010.pointList FastDual17_010.columns FastDual17_010.rows FastDual17_010.bound (by decide +kernel)
    FastDual17_010.column_mask FastDual17_010.checked hc F hF hroot hmin hout

theorem query269 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,6,8,9} := rep010 halph

def symmetry270 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query270 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,6,8,10} :=
  obstruction_transport link17 FastDual17_010.points {1,6,8,10} symmetry270
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry270 (by decide +kernel)) (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_011.pointList FastDual17_011.columns FastDual17_011.rows FastDual17_011.bound (by decide +kernel)
    FastDual17_011.column_mask FastDual17_011.checked hc F hF hroot hmin hout

theorem query271 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,6,8,11} := rep011 halph

theorem rep012 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_012.pointList FastDual17_012.columns FastDual17_012.rows FastDual17_012.bound (by decide +kernel)
    FastDual17_012.column_mask FastDual17_012.checked hc F hF hroot hmin hout

theorem query272 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,6,9,10} := rep012 halph

theorem rep013 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_013.pointList FastDual17_013.columns FastDual17_013.rows FastDual17_013.bound (by decide +kernel)
    FastDual17_013.column_mask FastDual17_013.checked hc F hF hroot hmin hout

theorem query273 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,6,9,11} := rep013 halph

def symmetry274 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query274 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,6,10,11} :=
  obstruction_transport link17 FastDual17_013.points {1,6,10,11} symmetry274
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry274 (by decide +kernel)) (by decide +kernel) (rep013 halph)

theorem rep014 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_014.pointList FastDual17_014.columns FastDual17_014.rows FastDual17_014.bound (by decide +kernel)
    FastDual17_014.column_mask FastDual17_014.checked hc F hF hroot hmin hout

theorem query275 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,7,8,9} := rep014 halph

def symmetry410 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query410 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {3,6,8,10} :=
  obstruction_transport link17 FastDual17_014.points {3,6,8,10} symmetry410
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry410 (by decide +kernel)) (by decide +kernel) (rep014 halph)

theorem rep015 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_015.pointList FastDual17_015.columns FastDual17_015.rows FastDual17_015.bound (by decide +kernel)
    FastDual17_015.column_mask FastDual17_015.checked hc F hF hroot hmin hout

theorem query276 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,7,8,10} := rep015 halph

def symmetry409 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query409 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {3,6,8,9} :=
  obstruction_transport link17 FastDual17_015.points {3,6,8,9} symmetry409
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry409 (by decide +kernel)) (by decide +kernel) (rep015 halph)

theorem rep016 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_016.pointList FastDual17_016.columns FastDual17_016.rows FastDual17_016.bound (by decide +kernel)
    FastDual17_016.column_mask FastDual17_016.checked hc F hF hroot hmin hout

theorem query277 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,7,8,11} := rep016 halph

def symmetry411 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query411 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {3,6,8,11} :=
  obstruction_transport link17 FastDual17_016.points {3,6,8,11} symmetry411
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry411 (by decide +kernel)) (by decide +kernel) (rep016 halph)

theorem rep017 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_017.pointList FastDual17_017.columns FastDual17_017.rows FastDual17_017.bound (by decide +kernel)
    FastDual17_017.column_mask FastDual17_017.checked hc F hF hroot hmin hout

theorem query278 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,7,9,10} := rep017 halph

def symmetry412 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query412 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {3,6,9,10} :=
  obstruction_transport link17 FastDual17_017.points {3,6,9,10} symmetry412
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry412 (by decide +kernel)) (by decide +kernel) (rep017 halph)

theorem rep018 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_018.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_018.pointList FastDual17_018.columns FastDual17_018.rows FastDual17_018.bound (by decide +kernel)
    FastDual17_018.column_mask FastDual17_018.checked hc F hF hroot hmin hout

theorem query279 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,7,9,11} := rep018 halph

def symmetry414 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query414 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {3,6,10,11} :=
  obstruction_transport link17 FastDual17_018.points {3,6,10,11} symmetry414
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry414 (by decide +kernel)) (by decide +kernel) (rep018 halph)

theorem rep019 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_019.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_019.pointList FastDual17_019.columns FastDual17_019.rows FastDual17_019.bound (by decide +kernel)
    FastDual17_019.column_mask FastDual17_019.checked hc F hF hroot hmin hout

theorem query280 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {1,7,10,11} := rep019 halph

def symmetry413 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query413 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {3,6,9,11} :=
  obstruction_transport link17 FastDual17_019.points {3,6,9,11} symmetry413
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry413 (by decide +kernel)) (by decide +kernel) (rep019 halph)

theorem rep020 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_020.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_020.pointList FastDual17_020.columns FastDual17_020.rows FastDual17_020.bound (by decide +kernel)
    FastDual17_020.column_mask FastDual17_020.checked hc F hF hroot hmin hout

theorem query415 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {3,7,8,9} := rep020 halph

def symmetry416 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query416 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {3,7,8,10} :=
  obstruction_transport link17 FastDual17_020.points {3,7,8,10} symmetry416
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry416 (by decide +kernel)) (by decide +kernel) (rep020 halph)

theorem rep021 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_021.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_021.pointList FastDual17_021.columns FastDual17_021.rows FastDual17_021.bound (by decide +kernel)
    FastDual17_021.column_mask FastDual17_021.checked hc F hF hroot hmin hout

theorem query417 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {3,7,8,11} := rep021 halph

theorem rep022 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_022.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_022.pointList FastDual17_022.columns FastDual17_022.rows FastDual17_022.bound (by decide +kernel)
    FastDual17_022.column_mask FastDual17_022.checked hc F hF hroot hmin hout

theorem query418 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {3,7,9,10} := rep022 halph

theorem rep023 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_023.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_023.pointList FastDual17_023.columns FastDual17_023.rows FastDual17_023.bound (by decide +kernel)
    FastDual17_023.column_mask FastDual17_023.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {3,7,9,11} := rep023 halph

def symmetry420 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query420 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {3,7,10,11} :=
  obstruction_transport link17 FastDual17_023.points {3,7,10,11} symmetry420
    (by decide +kernel) (root_symmetry_of_codes rootCodes link17 root_binding symmetry420 (by decide +kernel)) (by decide +kernel) (rep023 halph)

theorem rep024 (halph : AlphabetComplete link17 alphabets) :
    ActualObstruction link17 FastDual17_024.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link17 rootCodes root_binding alphabets halph nonincident_complete
    FastDual17_024.pointList FastDual17_024.columns FastDual17_024.rows FastDual17_024.bound (by decide +kernel)
    FastDual17_024.column_mask FastDual17_024.checked hc F hF hroot hmin hout

theorem query494 (halph : AlphabetComplete link17 alphabets) : ActualObstruction link17 {8,9,10,11} := rep024 halph

def dualQuads : List (Finset Point) := [{1,3,6,8},{1,6,7,8},{1,3,6,9},{1,6,7,10},{1,3,6,10},{1,6,7,9},{1,3,6,11},{1,6,7,11},{1,3,7,8},{3,6,7,8},{1,3,7,9},{3,6,7,10},{1,3,7,10},{3,6,7,9},{1,3,7,11},{3,6,7,11},{1,3,8,10},{6,7,8,9},{1,3,9,11},{6,7,10,11},{1,6,8,9},{1,6,8,10},{1,6,8,11},{1,6,9,10},{1,6,9,11},{1,6,10,11},{1,7,8,9},{3,6,8,10},{1,7,8,10},{3,6,8,9},{1,7,8,11},{3,6,8,11},{1,7,9,10},{3,6,9,10},{1,7,9,11},{3,6,10,11},{1,7,10,11},{3,6,9,11},{3,7,8,9},{3,7,8,10},{3,7,8,11},{3,7,9,10},{3,7,9,11},{3,7,10,11},{8,9,10,11}]

theorem dual_actual (halph : AlphabetComplete link17 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link17 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query215 halph
  · exact query265 halph
  · exact query216 halph
  · exact query267 halph
  · exact query217 halph
  · exact query266 halph
  · exact query218 halph
  · exact query268 halph
  · exact query219 halph
  · exact query405 halph
  · exact query220 halph
  · exact query407 halph
  · exact query221 halph
  · exact query406 halph
  · exact query222 halph
  · exact query408 halph
  · exact query224 halph
  · exact query480 halph
  · exact query227 halph
  · exact query485 halph
  · exact query269 halph
  · exact query270 halph
  · exact query271 halph
  · exact query272 halph
  · exact query273 halph
  · exact query274 halph
  · exact query275 halph
  · exact query410 halph
  · exact query276 halph
  · exact query409 halph
  · exact query277 halph
  · exact query411 halph
  · exact query278 halph
  · exact query412 halph
  · exact query279 halph
  · exact query414 halph
  · exact query280 halph
  · exact query413 halph
  · exact query415 halph
  · exact query416 halph
  · exact query417 halph
  · exact query418 halph
  · exact query419 halph
  · exact query420 halph
  · exact query494 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link17 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link17 Q :=
  class_census link17 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source17
