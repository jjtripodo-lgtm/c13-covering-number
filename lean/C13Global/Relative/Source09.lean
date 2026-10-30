import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source09
import C13Global.FastGroups.Source09Part00
import C13Global.FastGroups.Source09Part01
import C13Global.FastGroups.Source09Part02
namespace C13.Global.Relative.Source09
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source09
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link09 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link09 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link09 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link09 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_000.pointList FastDual09_000.columns FastDual09_000.rows FastDual09_000.bound (by decide +kernel)
    FastDual09_000.column_mask FastDual09_000.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,3,6,7} := rep000 halph

theorem rep001 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_001.pointList FastDual09_001.columns FastDual09_001.rows FastDual09_001.bound (by decide +kernel)
    FastDual09_001.column_mask FastDual09_001.checked hc F hF hroot hmin hout

theorem query299 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,3,6,8} := rep001 halph

def symmetry300 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query300 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,3,6,9} :=
  obstruction_transport link09 FastDual09_001.points {2,3,6,9} symmetry300
    (by decide +kernel) (root_symmetry_of_codes rootCodes link09 root_binding symmetry300 (by decide +kernel)) (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_002.pointList FastDual09_002.columns FastDual09_002.rows FastDual09_002.bound (by decide +kernel)
    FastDual09_002.column_mask FastDual09_002.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,3,6,11} := rep002 halph

theorem rep003 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_003.pointList FastDual09_003.columns FastDual09_003.rows FastDual09_003.bound (by decide +kernel)
    FastDual09_003.column_mask FastDual09_003.checked hc F hF hroot hmin hout

theorem query303 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,3,7,8} := rep003 halph

def symmetry304 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query304 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,3,7,9} :=
  obstruction_transport link09 FastDual09_003.points {2,3,7,9} symmetry304
    (by decide +kernel) (root_symmetry_of_codes rootCodes link09 root_binding symmetry304 (by decide +kernel)) (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_004.pointList FastDual09_004.columns FastDual09_004.rows FastDual09_004.bound (by decide +kernel)
    FastDual09_004.column_mask FastDual09_004.checked hc F hF hroot hmin hout

theorem query306 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,3,7,11} := rep004 halph

theorem rep005 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_005.pointList FastDual09_005.columns FastDual09_005.rows FastDual09_005.bound (by decide +kernel)
    FastDual09_005.column_mask FastDual09_005.checked hc F hF hroot hmin hout

theorem query307 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,3,8,9} := rep005 halph

theorem rep006 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_006.pointList FastDual09_006.columns FastDual09_006.rows FastDual09_006.bound (by decide +kernel)
    FastDual09_006.column_mask FastDual09_006.checked hc F hF hroot hmin hout

theorem query349 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,6,7,8} := rep006 halph

def symmetry406 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query406 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {3,6,7,9} :=
  obstruction_transport link09 FastDual09_006.points {3,6,7,9} symmetry406
    (by decide +kernel) (root_symmetry_of_codes rootCodes link09 root_binding symmetry406 (by decide +kernel)) (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_007.pointList FastDual09_007.columns FastDual09_007.rows FastDual09_007.bound (by decide +kernel)
    FastDual09_007.column_mask FastDual09_007.checked hc F hF hroot hmin hout

theorem query350 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,6,7,9} := rep007 halph

def symmetry405 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query405 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {3,6,7,8} :=
  obstruction_transport link09 FastDual09_007.points {3,6,7,8} symmetry405
    (by decide +kernel) (root_symmetry_of_codes rootCodes link09 root_binding symmetry405 (by decide +kernel)) (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_008.pointList FastDual09_008.columns FastDual09_008.rows FastDual09_008.bound (by decide +kernel)
    FastDual09_008.column_mask FastDual09_008.checked hc F hF hroot hmin hout

theorem query352 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,6,7,11} := rep008 halph

def symmetry408 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query408 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {3,6,7,11} :=
  obstruction_transport link09 FastDual09_008.points {3,6,7,11} symmetry408
    (by decide +kernel) (root_symmetry_of_codes rootCodes link09 root_binding symmetry408 (by decide +kernel)) (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_009.pointList FastDual09_009.columns FastDual09_009.rows FastDual09_009.bound (by decide +kernel)
    FastDual09_009.column_mask FastDual09_009.checked hc F hF hroot hmin hout

theorem query353 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,6,8,9} := rep009 halph

def symmetry409 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query409 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {3,6,8,9} :=
  obstruction_transport link09 FastDual09_009.points {3,6,8,9} symmetry409
    (by decide +kernel) (root_symmetry_of_codes rootCodes link09 root_binding symmetry409 (by decide +kernel)) (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_010.pointList FastDual09_010.columns FastDual09_010.rows FastDual09_010.bound (by decide +kernel)
    FastDual09_010.column_mask FastDual09_010.checked hc F hF hroot hmin hout

theorem query355 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,6,8,11} := rep010 halph

def symmetry413 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query413 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {3,6,9,11} :=
  obstruction_transport link09 FastDual09_010.points {3,6,9,11} symmetry413
    (by decide +kernel) (root_symmetry_of_codes rootCodes link09 root_binding symmetry413 (by decide +kernel)) (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_011.pointList FastDual09_011.columns FastDual09_011.rows FastDual09_011.bound (by decide +kernel)
    FastDual09_011.column_mask FastDual09_011.checked hc F hF hroot hmin hout

theorem query357 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,6,9,11} := rep011 halph

def symmetry411 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query411 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {3,6,8,11} :=
  obstruction_transport link09 FastDual09_011.points {3,6,8,11} symmetry411
    (by decide +kernel) (root_symmetry_of_codes rootCodes link09 root_binding symmetry411 (by decide +kernel)) (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_012.pointList FastDual09_012.columns FastDual09_012.rows FastDual09_012.bound (by decide +kernel)
    FastDual09_012.column_mask FastDual09_012.checked hc F hF hroot hmin hout

theorem query359 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,7,8,9} := rep012 halph

def symmetry415 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query415 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {3,7,8,9} :=
  obstruction_transport link09 FastDual09_012.points {3,7,8,9} symmetry415
    (by decide +kernel) (root_symmetry_of_codes rootCodes link09 root_binding symmetry415 (by decide +kernel)) (by decide +kernel) (rep012 halph)

theorem rep013 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_013.pointList FastDual09_013.columns FastDual09_013.rows FastDual09_013.bound (by decide +kernel)
    FastDual09_013.column_mask FastDual09_013.checked hc F hF hroot hmin hout

theorem query361 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,7,8,11} := rep013 halph

def symmetry419 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query419 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {3,7,9,11} :=
  obstruction_transport link09 FastDual09_013.points {3,7,9,11} symmetry419
    (by decide +kernel) (root_symmetry_of_codes rootCodes link09 root_binding symmetry419 (by decide +kernel)) (by decide +kernel) (rep013 halph)

theorem rep014 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_014.pointList FastDual09_014.columns FastDual09_014.rows FastDual09_014.bound (by decide +kernel)
    FastDual09_014.column_mask FastDual09_014.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {2,7,9,11} := rep014 halph

def symmetry417 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query417 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {3,7,8,11} :=
  obstruction_transport link09 FastDual09_014.points {3,7,8,11} symmetry417
    (by decide +kernel) (root_symmetry_of_codes rootCodes link09 root_binding symmetry417 (by decide +kernel)) (by decide +kernel) (rep014 halph)

theorem rep015 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_015.pointList FastDual09_015.columns FastDual09_015.rows FastDual09_015.bound (by decide +kernel)
    FastDual09_015.column_mask FastDual09_015.checked hc F hF hroot hmin hout

theorem query480 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {6,7,8,9} := rep015 halph

theorem rep016 (halph : AlphabetComplete link09 alphabets) :
    ActualObstruction link09 FastDual09_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link09 rootCodes root_binding alphabets halph nonincident_complete
    FastDual09_016.pointList FastDual09_016.columns FastDual09_016.rows FastDual09_016.bound (by decide +kernel)
    FastDual09_016.column_mask FastDual09_016.checked hc F hF hroot hmin hout

theorem query487 (halph : AlphabetComplete link09 alphabets) : ActualObstruction link09 {6,8,9,11} := rep016 halph

def dualQuads : List (Finset Point) := [{2,3,6,7},{2,3,6,8},{2,3,6,9},{2,3,6,11},{2,3,7,8},{2,3,7,9},{2,3,7,11},{2,3,8,9},{2,6,7,8},{3,6,7,9},{2,6,7,9},{3,6,7,8},{2,6,7,11},{3,6,7,11},{2,6,8,9},{3,6,8,9},{2,6,8,11},{3,6,9,11},{2,6,9,11},{3,6,8,11},{2,7,8,9},{3,7,8,9},{2,7,8,11},{3,7,9,11},{2,7,9,11},{3,7,8,11},{6,7,8,9},{6,8,9,11}]

theorem dual_actual (halph : AlphabetComplete link09 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link09 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query298 halph
  · exact query299 halph
  · exact query300 halph
  · exact query302 halph
  · exact query303 halph
  · exact query304 halph
  · exact query306 halph
  · exact query307 halph
  · exact query349 halph
  · exact query406 halph
  · exact query350 halph
  · exact query405 halph
  · exact query352 halph
  · exact query408 halph
  · exact query353 halph
  · exact query409 halph
  · exact query355 halph
  · exact query413 halph
  · exact query357 halph
  · exact query411 halph
  · exact query359 halph
  · exact query415 halph
  · exact query361 halph
  · exact query419 halph
  · exact query363 halph
  · exact query417 halph
  · exact query480 halph
  · exact query487 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link09 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link09 Q :=
  class_census link09 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source09
