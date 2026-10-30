import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source15
import C13Global.FastGroups.Source15Part00
import C13Global.FastGroups.Source15Part01
namespace C13.Global.Relative.Source15
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source15
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link15 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link15 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link15 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link15 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link15 alphabets) :
    ActualObstruction link15 FastDual15_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link15 rootCodes root_binding alphabets halph nonincident_complete
    FastDual15_000.pointList FastDual15_000.columns FastDual15_000.rows FastDual15_000.bound (by decide +kernel)
    FastDual15_000.column_mask FastDual15_000.checked hc F hF hroot hmin hout

theorem query215 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,3,6,8} := rep000 halph

def symmetry217 : Equiv.Perm Point where
  toFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  invFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query217 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,3,6,10} :=
  obstruction_transport link15 FastDual15_000.points {1,3,6,10} symmetry217
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry217 (by decide +kernel)) (by decide +kernel) (rep000 halph)

def symmetry220 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query220 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,3,7,9} :=
  obstruction_transport link15 FastDual15_000.points {1,3,7,9} symmetry220
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry220 (by decide +kernel)) (by decide +kernel) (rep000 halph)

def symmetry222 : Equiv.Perm Point where
  toFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  invFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query222 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,3,7,11} :=
  obstruction_transport link15 FastDual15_000.points {1,3,7,11} symmetry222
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry222 (by decide +kernel)) (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link15 alphabets) :
    ActualObstruction link15 FastDual15_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link15 rootCodes root_binding alphabets halph nonincident_complete
    FastDual15_001.pointList FastDual15_001.columns FastDual15_001.rows FastDual15_001.bound (by decide +kernel)
    FastDual15_001.column_mask FastDual15_001.checked hc F hF hroot hmin hout

theorem query216 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,3,6,9} := rep001 halph

def symmetry218 : Equiv.Perm Point where
  toFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  invFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query218 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,3,6,11} :=
  obstruction_transport link15 FastDual15_001.points {1,3,6,11} symmetry218
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry218 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry219 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query219 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,3,7,8} :=
  obstruction_transport link15 FastDual15_001.points {1,3,7,8} symmetry219
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry219 (by decide +kernel)) (by decide +kernel) (rep001 halph)

def symmetry221 : Equiv.Perm Point where
  toFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  invFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query221 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,3,7,10} :=
  obstruction_transport link15 FastDual15_001.points {1,3,7,10} symmetry221
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry221 (by decide +kernel)) (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link15 alphabets) :
    ActualObstruction link15 FastDual15_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link15 rootCodes root_binding alphabets halph nonincident_complete
    FastDual15_002.pointList FastDual15_002.columns FastDual15_002.rows FastDual15_002.bound (by decide +kernel)
    FastDual15_002.column_mask FastDual15_002.checked hc F hF hroot hmin hout

theorem query224 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,3,8,10} := rep002 halph

def symmetry227 : Equiv.Perm Point where
  toFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  invFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query227 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,3,9,11} :=
  obstruction_transport link15 FastDual15_002.points {1,3,9,11} symmetry227
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry227 (by decide +kernel)) (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link15 alphabets) :
    ActualObstruction link15 FastDual15_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link15 rootCodes root_binding alphabets halph nonincident_complete
    FastDual15_003.pointList FastDual15_003.columns FastDual15_003.rows FastDual15_003.bound (by decide +kernel)
    FastDual15_003.column_mask FastDual15_003.checked hc F hF hroot hmin hout

theorem query265 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,6,7,8} := rep003 halph

def symmetry266 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query266 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,6,7,9} :=
  obstruction_transport link15 FastDual15_003.points {1,6,7,9} symmetry266
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry266 (by decide +kernel)) (by decide +kernel) (rep003 halph)

def symmetry407 : Equiv.Perm Point where
  toFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  invFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query407 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {3,6,7,10} :=
  obstruction_transport link15 FastDual15_003.points {3,6,7,10} symmetry407
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry407 (by decide +kernel)) (by decide +kernel) (rep003 halph)

def symmetry408 : Equiv.Perm Point where
  toFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  invFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query408 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {3,6,7,11} :=
  obstruction_transport link15 FastDual15_003.points {3,6,7,11} symmetry408
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry408 (by decide +kernel)) (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link15 alphabets) :
    ActualObstruction link15 FastDual15_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link15 rootCodes root_binding alphabets halph nonincident_complete
    FastDual15_004.pointList FastDual15_004.columns FastDual15_004.rows FastDual15_004.bound (by decide +kernel)
    FastDual15_004.column_mask FastDual15_004.checked hc F hF hroot hmin hout

theorem query267 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,6,7,10} := rep004 halph

def symmetry268 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query268 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,6,7,11} :=
  obstruction_transport link15 FastDual15_004.points {1,6,7,11} symmetry268
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry268 (by decide +kernel)) (by decide +kernel) (rep004 halph)

def symmetry405 : Equiv.Perm Point where
  toFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  invFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query405 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {3,6,7,8} :=
  obstruction_transport link15 FastDual15_004.points {3,6,7,8} symmetry405
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry405 (by decide +kernel)) (by decide +kernel) (rep004 halph)

def symmetry406 : Equiv.Perm Point where
  toFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  invFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query406 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {3,6,7,9} :=
  obstruction_transport link15 FastDual15_004.points {3,6,7,9} symmetry406
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry406 (by decide +kernel)) (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link15 alphabets) :
    ActualObstruction link15 FastDual15_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link15 rootCodes root_binding alphabets halph nonincident_complete
    FastDual15_005.pointList FastDual15_005.columns FastDual15_005.rows FastDual15_005.bound (by decide +kernel)
    FastDual15_005.column_mask FastDual15_005.checked hc F hF hroot hmin hout

theorem query269 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,6,8,9} := rep005 halph

def symmetry275 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query275 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,7,8,9} :=
  obstruction_transport link15 FastDual15_005.points {1,7,8,9} symmetry275
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry275 (by decide +kernel)) (by decide +kernel) (rep005 halph)

def symmetry414 : Equiv.Perm Point where
  toFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  invFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query414 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {3,6,10,11} :=
  obstruction_transport link15 FastDual15_005.points {3,6,10,11} symmetry414
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry414 (by decide +kernel)) (by decide +kernel) (rep005 halph)

def symmetry420 : Equiv.Perm Point where
  toFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  invFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query420 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {3,7,10,11} :=
  obstruction_transport link15 FastDual15_005.points {3,7,10,11} symmetry420
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry420 (by decide +kernel)) (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link15 alphabets) :
    ActualObstruction link15 FastDual15_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link15 rootCodes root_binding alphabets halph nonincident_complete
    FastDual15_006.pointList FastDual15_006.columns FastDual15_006.rows FastDual15_006.bound (by decide +kernel)
    FastDual15_006.column_mask FastDual15_006.checked hc F hF hroot hmin hout

theorem query270 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,6,8,10} := rep006 halph

def symmetry279 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query279 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,7,9,11} :=
  obstruction_transport link15 FastDual15_006.points {1,7,9,11} symmetry279
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry279 (by decide +kernel)) (by decide +kernel) (rep006 halph)

def symmetry410 : Equiv.Perm Point where
  toFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  invFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query410 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {3,6,8,10} :=
  obstruction_transport link15 FastDual15_006.points {3,6,8,10} symmetry410
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry410 (by decide +kernel)) (by decide +kernel) (rep006 halph)

def symmetry419 : Equiv.Perm Point where
  toFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  invFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query419 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {3,7,9,11} :=
  obstruction_transport link15 FastDual15_006.points {3,7,9,11} symmetry419
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry419 (by decide +kernel)) (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link15 alphabets) :
    ActualObstruction link15 FastDual15_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link15 rootCodes root_binding alphabets halph nonincident_complete
    FastDual15_007.pointList FastDual15_007.columns FastDual15_007.rows FastDual15_007.bound (by decide +kernel)
    FastDual15_007.column_mask FastDual15_007.checked hc F hF hroot hmin hout

theorem query271 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,6,8,11} := rep007 halph

def symmetry278 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query278 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,7,9,10} :=
  obstruction_transport link15 FastDual15_007.points {1,7,9,10} symmetry278
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry278 (by decide +kernel)) (by decide +kernel) (rep007 halph)

def symmetry412 : Equiv.Perm Point where
  toFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  invFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query412 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {3,6,9,10} :=
  obstruction_transport link15 FastDual15_007.points {3,6,9,10} symmetry412
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry412 (by decide +kernel)) (by decide +kernel) (rep007 halph)

def symmetry417 : Equiv.Perm Point where
  toFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  invFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query417 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {3,7,8,11} :=
  obstruction_transport link15 FastDual15_007.points {3,7,8,11} symmetry417
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry417 (by decide +kernel)) (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link15 alphabets) :
    ActualObstruction link15 FastDual15_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link15 rootCodes root_binding alphabets halph nonincident_complete
    FastDual15_008.pointList FastDual15_008.columns FastDual15_008.rows FastDual15_008.bound (by decide +kernel)
    FastDual15_008.column_mask FastDual15_008.checked hc F hF hroot hmin hout

theorem query272 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,6,9,10} := rep008 halph

def symmetry277 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query277 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,7,8,11} :=
  obstruction_transport link15 FastDual15_008.points {1,7,8,11} symmetry277
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry277 (by decide +kernel)) (by decide +kernel) (rep008 halph)

def symmetry411 : Equiv.Perm Point where
  toFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  invFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query411 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {3,6,8,11} :=
  obstruction_transport link15 FastDual15_008.points {3,6,8,11} symmetry411
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry411 (by decide +kernel)) (by decide +kernel) (rep008 halph)

def symmetry418 : Equiv.Perm Point where
  toFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  invFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query418 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {3,7,9,10} :=
  obstruction_transport link15 FastDual15_008.points {3,7,9,10} symmetry418
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry418 (by decide +kernel)) (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link15 alphabets) :
    ActualObstruction link15 FastDual15_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link15 rootCodes root_binding alphabets halph nonincident_complete
    FastDual15_009.pointList FastDual15_009.columns FastDual15_009.rows FastDual15_009.bound (by decide +kernel)
    FastDual15_009.column_mask FastDual15_009.checked hc F hF hroot hmin hout

theorem query273 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,6,9,11} := rep009 halph

def symmetry276 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query276 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,7,8,10} :=
  obstruction_transport link15 FastDual15_009.points {1,7,8,10} symmetry276
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry276 (by decide +kernel)) (by decide +kernel) (rep009 halph)

def symmetry413 : Equiv.Perm Point where
  toFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  invFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query413 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {3,6,9,11} :=
  obstruction_transport link15 FastDual15_009.points {3,6,9,11} symmetry413
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry413 (by decide +kernel)) (by decide +kernel) (rep009 halph)

def symmetry416 : Equiv.Perm Point where
  toFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  invFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query416 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {3,7,8,10} :=
  obstruction_transport link15 FastDual15_009.points {3,7,8,10} symmetry416
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry416 (by decide +kernel)) (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link15 alphabets) :
    ActualObstruction link15 FastDual15_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link15 rootCodes root_binding alphabets halph nonincident_complete
    FastDual15_010.pointList FastDual15_010.columns FastDual15_010.rows FastDual15_010.bound (by decide +kernel)
    FastDual15_010.column_mask FastDual15_010.checked hc F hF hroot hmin hout

theorem query274 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,6,10,11} := rep010 halph

def symmetry280 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query280 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {1,7,10,11} :=
  obstruction_transport link15 FastDual15_010.points {1,7,10,11} symmetry280
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry280 (by decide +kernel)) (by decide +kernel) (rep010 halph)

def symmetry409 : Equiv.Perm Point where
  toFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  invFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query409 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {3,6,8,9} :=
  obstruction_transport link15 FastDual15_010.points {3,6,8,9} symmetry409
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry409 (by decide +kernel)) (by decide +kernel) (rep010 halph)

def symmetry415 : Equiv.Perm Point where
  toFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  invFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query415 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {3,7,8,9} :=
  obstruction_transport link15 FastDual15_010.points {3,7,8,9} symmetry415
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry415 (by decide +kernel)) (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link15 alphabets) :
    ActualObstruction link15 FastDual15_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link15 rootCodes root_binding alphabets halph nonincident_complete
    FastDual15_011.pointList FastDual15_011.columns FastDual15_011.rows FastDual15_011.bound (by decide +kernel)
    FastDual15_011.column_mask FastDual15_011.checked hc F hF hroot hmin hout

theorem query480 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {6,7,8,9} := rep011 halph

def symmetry485 : Equiv.Perm Point where
  toFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  invFun := ![2,3,0,1,5,4,7,6,11,10,9,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query485 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {6,7,10,11} :=
  obstruction_transport link15 FastDual15_011.points {6,7,10,11} symmetry485
    (by decide +kernel) (root_symmetry_of_codes rootCodes link15 root_binding symmetry485 (by decide +kernel)) (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link15 alphabets) :
    ActualObstruction link15 FastDual15_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link15 rootCodes root_binding alphabets halph nonincident_complete
    FastDual15_012.pointList FastDual15_012.columns FastDual15_012.rows FastDual15_012.bound (by decide +kernel)
    FastDual15_012.column_mask FastDual15_012.checked hc F hF hroot hmin hout

theorem query494 (halph : AlphabetComplete link15 alphabets) : ActualObstruction link15 {8,9,10,11} := rep012 halph

def dualQuads : List (Finset Point) := [{1,3,6,8},{1,3,6,10},{1,3,7,9},{1,3,7,11},{1,3,6,9},{1,3,6,11},{1,3,7,8},{1,3,7,10},{1,3,8,10},{1,3,9,11},{1,6,7,8},{1,6,7,9},{3,6,7,10},{3,6,7,11},{1,6,7,10},{1,6,7,11},{3,6,7,8},{3,6,7,9},{1,6,8,9},{1,7,8,9},{3,6,10,11},{3,7,10,11},{1,6,8,10},{1,7,9,11},{3,6,8,10},{3,7,9,11},{1,6,8,11},{1,7,9,10},{3,6,9,10},{3,7,8,11},{1,6,9,10},{1,7,8,11},{3,6,8,11},{3,7,9,10},{1,6,9,11},{1,7,8,10},{3,6,9,11},{3,7,8,10},{1,6,10,11},{1,7,10,11},{3,6,8,9},{3,7,8,9},{6,7,8,9},{6,7,10,11},{8,9,10,11}]

theorem dual_actual (halph : AlphabetComplete link15 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link15 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query215 halph
  · exact query217 halph
  · exact query220 halph
  · exact query222 halph
  · exact query216 halph
  · exact query218 halph
  · exact query219 halph
  · exact query221 halph
  · exact query224 halph
  · exact query227 halph
  · exact query265 halph
  · exact query266 halph
  · exact query407 halph
  · exact query408 halph
  · exact query267 halph
  · exact query268 halph
  · exact query405 halph
  · exact query406 halph
  · exact query269 halph
  · exact query275 halph
  · exact query414 halph
  · exact query420 halph
  · exact query270 halph
  · exact query279 halph
  · exact query410 halph
  · exact query419 halph
  · exact query271 halph
  · exact query278 halph
  · exact query412 halph
  · exact query417 halph
  · exact query272 halph
  · exact query277 halph
  · exact query411 halph
  · exact query418 halph
  · exact query273 halph
  · exact query276 halph
  · exact query413 halph
  · exact query416 halph
  · exact query274 halph
  · exact query280 halph
  · exact query409 halph
  · exact query415 halph
  · exact query480 halph
  · exact query485 halph
  · exact query494 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link15 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link15 Q :=
  class_census link15 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source15
