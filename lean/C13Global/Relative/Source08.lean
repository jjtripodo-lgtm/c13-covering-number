import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source08
import C13Global.FastGroups.Source08Part00
import C13Global.FastGroups.Source08Part01
namespace C13.Global.Relative.Source08
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source08
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link08 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link08 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link08 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link08 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link08 alphabets) :
    ActualObstruction link08 FastDual08_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link08 rootCodes root_binding alphabets halph nonincident_complete
    FastDual08_000.pointList FastDual08_000.columns FastDual08_000.rows FastDual08_000.bound (by decide +kernel)
    FastDual08_000.column_mask FastDual08_000.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,3,6,7} := rep000 halph

theorem rep001 (halph : AlphabetComplete link08 alphabets) :
    ActualObstruction link08 FastDual08_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link08 rootCodes root_binding alphabets halph nonincident_complete
    FastDual08_001.pointList FastDual08_001.columns FastDual08_001.rows FastDual08_001.bound (by decide +kernel)
    FastDual08_001.column_mask FastDual08_001.checked hc F hF hroot hmin hout

theorem query300 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,3,6,9} := rep001 halph

def symmetry304 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query304 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,3,7,9} :=
  obstruction_transport link08 FastDual08_001.points {2,3,7,9} symmetry304
    (by decide +kernel) (root_symmetry_of_codes rootCodes link08 root_binding symmetry304 (by decide +kernel)) (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link08 alphabets) :
    ActualObstruction link08 FastDual08_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link08 rootCodes root_binding alphabets halph nonincident_complete
    FastDual08_002.pointList FastDual08_002.columns FastDual08_002.rows FastDual08_002.bound (by decide +kernel)
    FastDual08_002.column_mask FastDual08_002.checked hc F hF hroot hmin hout

theorem query301 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,3,6,10} := rep002 halph

def symmetry306 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query306 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,3,7,11} :=
  obstruction_transport link08 FastDual08_002.points {2,3,7,11} symmetry306
    (by decide +kernel) (root_symmetry_of_codes rootCodes link08 root_binding symmetry306 (by decide +kernel)) (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link08 alphabets) :
    ActualObstruction link08 FastDual08_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link08 rootCodes root_binding alphabets halph nonincident_complete
    FastDual08_003.pointList FastDual08_003.columns FastDual08_003.rows FastDual08_003.bound (by decide +kernel)
    FastDual08_003.column_mask FastDual08_003.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,3,6,11} := rep003 halph

def symmetry305 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query305 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,3,7,10} :=
  obstruction_transport link08 FastDual08_003.points {2,3,7,10} symmetry305
    (by decide +kernel) (root_symmetry_of_codes rootCodes link08 root_binding symmetry305 (by decide +kernel)) (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link08 alphabets) :
    ActualObstruction link08 FastDual08_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link08 rootCodes root_binding alphabets halph nonincident_complete
    FastDual08_004.pointList FastDual08_004.columns FastDual08_004.rows FastDual08_004.bound (by decide +kernel)
    FastDual08_004.column_mask FastDual08_004.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,3,10,11} := rep004 halph

theorem rep005 (halph : AlphabetComplete link08 alphabets) :
    ActualObstruction link08 FastDual08_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link08 rootCodes root_binding alphabets halph nonincident_complete
    FastDual08_005.pointList FastDual08_005.columns FastDual08_005.rows FastDual08_005.bound (by decide +kernel)
    FastDual08_005.column_mask FastDual08_005.checked hc F hF hroot hmin hout

theorem query350 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,6,7,9} := rep005 halph

def symmetry406 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query406 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {3,6,7,9} :=
  obstruction_transport link08 FastDual08_005.points {3,6,7,9} symmetry406
    (by decide +kernel) (root_symmetry_of_codes rootCodes link08 root_binding symmetry406 (by decide +kernel)) (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link08 alphabets) :
    ActualObstruction link08 FastDual08_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link08 rootCodes root_binding alphabets halph nonincident_complete
    FastDual08_006.pointList FastDual08_006.columns FastDual08_006.rows FastDual08_006.bound (by decide +kernel)
    FastDual08_006.column_mask FastDual08_006.checked hc F hF hroot hmin hout

theorem query351 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,6,7,10} := rep006 halph

def symmetry408 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query408 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {3,6,7,11} :=
  obstruction_transport link08 FastDual08_006.points {3,6,7,11} symmetry408
    (by decide +kernel) (root_symmetry_of_codes rootCodes link08 root_binding symmetry408 (by decide +kernel)) (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link08 alphabets) :
    ActualObstruction link08 FastDual08_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link08 rootCodes root_binding alphabets halph nonincident_complete
    FastDual08_007.pointList FastDual08_007.columns FastDual08_007.rows FastDual08_007.bound (by decide +kernel)
    FastDual08_007.column_mask FastDual08_007.checked hc F hF hroot hmin hout

theorem query352 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,6,7,11} := rep007 halph

def symmetry407 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query407 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {3,6,7,10} :=
  obstruction_transport link08 FastDual08_007.points {3,6,7,10} symmetry407
    (by decide +kernel) (root_symmetry_of_codes rootCodes link08 root_binding symmetry407 (by decide +kernel)) (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link08 alphabets) :
    ActualObstruction link08 FastDual08_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link08 rootCodes root_binding alphabets halph nonincident_complete
    FastDual08_008.pointList FastDual08_008.columns FastDual08_008.rows FastDual08_008.bound (by decide +kernel)
    FastDual08_008.column_mask FastDual08_008.checked hc F hF hroot hmin hout

theorem query356 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,6,9,10} := rep008 halph

def symmetry419 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query419 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {3,7,9,11} :=
  obstruction_transport link08 FastDual08_008.points {3,7,9,11} symmetry419
    (by decide +kernel) (root_symmetry_of_codes rootCodes link08 root_binding symmetry419 (by decide +kernel)) (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link08 alphabets) :
    ActualObstruction link08 FastDual08_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link08 rootCodes root_binding alphabets halph nonincident_complete
    FastDual08_009.pointList FastDual08_009.columns FastDual08_009.rows FastDual08_009.bound (by decide +kernel)
    FastDual08_009.column_mask FastDual08_009.checked hc F hF hroot hmin hout

theorem query357 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,6,9,11} := rep009 halph

def symmetry418 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query418 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {3,7,9,10} :=
  obstruction_transport link08 FastDual08_009.points {3,7,9,10} symmetry418
    (by decide +kernel) (root_symmetry_of_codes rootCodes link08 root_binding symmetry418 (by decide +kernel)) (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link08 alphabets) :
    ActualObstruction link08 FastDual08_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link08 rootCodes root_binding alphabets halph nonincident_complete
    FastDual08_010.pointList FastDual08_010.columns FastDual08_010.rows FastDual08_010.bound (by decide +kernel)
    FastDual08_010.column_mask FastDual08_010.checked hc F hF hroot hmin hout

theorem query358 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,6,10,11} := rep010 halph

def symmetry420 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query420 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {3,7,10,11} :=
  obstruction_transport link08 FastDual08_010.points {3,7,10,11} symmetry420
    (by decide +kernel) (root_symmetry_of_codes rootCodes link08 root_binding symmetry420 (by decide +kernel)) (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link08 alphabets) :
    ActualObstruction link08 FastDual08_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link08 rootCodes root_binding alphabets halph nonincident_complete
    FastDual08_011.pointList FastDual08_011.columns FastDual08_011.rows FastDual08_011.bound (by decide +kernel)
    FastDual08_011.column_mask FastDual08_011.checked hc F hF hroot hmin hout

theorem query362 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,7,9,10} := rep011 halph

def symmetry413 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query413 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {3,6,9,11} :=
  obstruction_transport link08 FastDual08_011.points {3,6,9,11} symmetry413
    (by decide +kernel) (root_symmetry_of_codes rootCodes link08 root_binding symmetry413 (by decide +kernel)) (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link08 alphabets) :
    ActualObstruction link08 FastDual08_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link08 rootCodes root_binding alphabets halph nonincident_complete
    FastDual08_012.pointList FastDual08_012.columns FastDual08_012.rows FastDual08_012.bound (by decide +kernel)
    FastDual08_012.column_mask FastDual08_012.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,7,9,11} := rep012 halph

def symmetry412 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query412 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {3,6,9,10} :=
  obstruction_transport link08 FastDual08_012.points {3,6,9,10} symmetry412
    (by decide +kernel) (root_symmetry_of_codes rootCodes link08 root_binding symmetry412 (by decide +kernel)) (by decide +kernel) (rep012 halph)

theorem rep013 (halph : AlphabetComplete link08 alphabets) :
    ActualObstruction link08 FastDual08_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link08 rootCodes root_binding alphabets halph nonincident_complete
    FastDual08_013.pointList FastDual08_013.columns FastDual08_013.rows FastDual08_013.bound (by decide +kernel)
    FastDual08_013.column_mask FastDual08_013.checked hc F hF hroot hmin hout

theorem query364 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {2,7,10,11} := rep013 halph

def symmetry414 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query414 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {3,6,10,11} :=
  obstruction_transport link08 FastDual08_013.points {3,6,10,11} symmetry414
    (by decide +kernel) (root_symmetry_of_codes rootCodes link08 root_binding symmetry414 (by decide +kernel)) (by decide +kernel) (rep013 halph)

theorem rep014 (halph : AlphabetComplete link08 alphabets) :
    ActualObstruction link08 FastDual08_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link08 rootCodes root_binding alphabets halph nonincident_complete
    FastDual08_014.pointList FastDual08_014.columns FastDual08_014.rows FastDual08_014.bound (by decide +kernel)
    FastDual08_014.column_mask FastDual08_014.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link08 alphabets) : ActualObstruction link08 {6,7,10,11} := rep014 halph

def dualQuads : List (Finset Point) := [{2,3,6,7},{2,3,6,9},{2,3,7,9},{2,3,6,10},{2,3,7,11},{2,3,6,11},{2,3,7,10},{2,3,10,11},{2,6,7,9},{3,6,7,9},{2,6,7,10},{3,6,7,11},{2,6,7,11},{3,6,7,10},{2,6,9,10},{3,7,9,11},{2,6,9,11},{3,7,9,10},{2,6,10,11},{3,7,10,11},{2,7,9,10},{3,6,9,11},{2,7,9,11},{3,6,9,10},{2,7,10,11},{3,6,10,11},{6,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link08 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link08 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query298 halph
  · exact query300 halph
  · exact query304 halph
  · exact query301 halph
  · exact query306 halph
  · exact query302 halph
  · exact query305 halph
  · exact query312 halph
  · exact query350 halph
  · exact query406 halph
  · exact query351 halph
  · exact query408 halph
  · exact query352 halph
  · exact query407 halph
  · exact query356 halph
  · exact query419 halph
  · exact query357 halph
  · exact query418 halph
  · exact query358 halph
  · exact query420 halph
  · exact query362 halph
  · exact query413 halph
  · exact query363 halph
  · exact query412 halph
  · exact query364 halph
  · exact query414 halph
  · exact query485 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link08 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link08 Q :=
  class_census link08 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source08
