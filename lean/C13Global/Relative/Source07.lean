import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source07
import C13Global.FastGroups.Source07Part00
import C13Global.FastGroups.Source07Part01
namespace C13.Global.Relative.Source07
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source07
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link07 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link07 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link07 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link07 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link07 alphabets) :
    ActualObstruction link07 FastDual07_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link07 rootCodes root_binding alphabets halph nonincident_complete
    FastDual07_000.pointList FastDual07_000.columns FastDual07_000.rows FastDual07_000.bound (by decide +kernel)
    FastDual07_000.column_mask FastDual07_000.checked hc F hF hroot hmin hout

theorem query405 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {3,6,7,8} := rep000 halph

def symmetry406 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query406 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {3,6,7,9} :=
  obstruction_transport link07 FastDual07_000.points {3,6,7,9} symmetry406
    (by decide +kernel) (root_symmetry_of_codes rootCodes link07 root_binding symmetry406 (by decide +kernel)) (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link07 alphabets) :
    ActualObstruction link07 FastDual07_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link07 rootCodes root_binding alphabets halph nonincident_complete
    FastDual07_001.pointList FastDual07_001.columns FastDual07_001.rows FastDual07_001.bound (by decide +kernel)
    FastDual07_001.column_mask FastDual07_001.checked hc F hF hroot hmin hout

theorem query407 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {3,6,7,10} := rep001 halph

def symmetry408 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query408 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {3,6,7,11} :=
  obstruction_transport link07 FastDual07_001.points {3,6,7,11} symmetry408
    (by decide +kernel) (root_symmetry_of_codes rootCodes link07 root_binding symmetry408 (by decide +kernel)) (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link07 alphabets) :
    ActualObstruction link07 FastDual07_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link07 rootCodes root_binding alphabets halph nonincident_complete
    FastDual07_002.pointList FastDual07_002.columns FastDual07_002.rows FastDual07_002.bound (by decide +kernel)
    FastDual07_002.column_mask FastDual07_002.checked hc F hF hroot hmin hout

theorem query409 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {3,6,8,9} := rep002 halph

def symmetry415 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query415 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {3,7,8,9} :=
  obstruction_transport link07 FastDual07_002.points {3,7,8,9} symmetry415
    (by decide +kernel) (root_symmetry_of_codes rootCodes link07 root_binding symmetry415 (by decide +kernel)) (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link07 alphabets) :
    ActualObstruction link07 FastDual07_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link07 rootCodes root_binding alphabets halph nonincident_complete
    FastDual07_003.pointList FastDual07_003.columns FastDual07_003.rows FastDual07_003.bound (by decide +kernel)
    FastDual07_003.column_mask FastDual07_003.checked hc F hF hroot hmin hout

theorem query410 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {3,6,8,10} := rep003 halph

def symmetry419 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query419 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {3,7,9,11} :=
  obstruction_transport link07 FastDual07_003.points {3,7,9,11} symmetry419
    (by decide +kernel) (root_symmetry_of_codes rootCodes link07 root_binding symmetry419 (by decide +kernel)) (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link07 alphabets) :
    ActualObstruction link07 FastDual07_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link07 rootCodes root_binding alphabets halph nonincident_complete
    FastDual07_004.pointList FastDual07_004.columns FastDual07_004.rows FastDual07_004.bound (by decide +kernel)
    FastDual07_004.column_mask FastDual07_004.checked hc F hF hroot hmin hout

theorem query411 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {3,6,8,11} := rep004 halph

def symmetry418 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query418 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {3,7,9,10} :=
  obstruction_transport link07 FastDual07_004.points {3,7,9,10} symmetry418
    (by decide +kernel) (root_symmetry_of_codes rootCodes link07 root_binding symmetry418 (by decide +kernel)) (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link07 alphabets) :
    ActualObstruction link07 FastDual07_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link07 rootCodes root_binding alphabets halph nonincident_complete
    FastDual07_005.pointList FastDual07_005.columns FastDual07_005.rows FastDual07_005.bound (by decide +kernel)
    FastDual07_005.column_mask FastDual07_005.checked hc F hF hroot hmin hout

theorem query412 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {3,6,9,10} := rep005 halph

def symmetry417 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query417 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {3,7,8,11} :=
  obstruction_transport link07 FastDual07_005.points {3,7,8,11} symmetry417
    (by decide +kernel) (root_symmetry_of_codes rootCodes link07 root_binding symmetry417 (by decide +kernel)) (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link07 alphabets) :
    ActualObstruction link07 FastDual07_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link07 rootCodes root_binding alphabets halph nonincident_complete
    FastDual07_006.pointList FastDual07_006.columns FastDual07_006.rows FastDual07_006.bound (by decide +kernel)
    FastDual07_006.column_mask FastDual07_006.checked hc F hF hroot hmin hout

theorem query413 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {3,6,9,11} := rep006 halph

def symmetry416 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query416 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {3,7,8,10} :=
  obstruction_transport link07 FastDual07_006.points {3,7,8,10} symmetry416
    (by decide +kernel) (root_symmetry_of_codes rootCodes link07 root_binding symmetry416 (by decide +kernel)) (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link07 alphabets) :
    ActualObstruction link07 FastDual07_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link07 rootCodes root_binding alphabets halph nonincident_complete
    FastDual07_007.pointList FastDual07_007.columns FastDual07_007.rows FastDual07_007.bound (by decide +kernel)
    FastDual07_007.column_mask FastDual07_007.checked hc F hF hroot hmin hout

theorem query414 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {3,6,10,11} := rep007 halph

def symmetry420 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query420 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {3,7,10,11} :=
  obstruction_transport link07 FastDual07_007.points {3,7,10,11} symmetry420
    (by decide +kernel) (root_symmetry_of_codes rootCodes link07 root_binding symmetry420 (by decide +kernel)) (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link07 alphabets) :
    ActualObstruction link07 FastDual07_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link07 rootCodes root_binding alphabets halph nonincident_complete
    FastDual07_008.pointList FastDual07_008.columns FastDual07_008.rows FastDual07_008.bound (by decide +kernel)
    FastDual07_008.column_mask FastDual07_008.checked hc F hF hroot hmin hout

theorem query480 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {6,7,8,9} := rep008 halph

theorem rep009 (halph : AlphabetComplete link07 alphabets) :
    ActualObstruction link07 FastDual07_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link07 rootCodes root_binding alphabets halph nonincident_complete
    FastDual07_009.pointList FastDual07_009.columns FastDual07_009.rows FastDual07_009.bound (by decide +kernel)
    FastDual07_009.column_mask FastDual07_009.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {6,7,10,11} := rep009 halph

theorem rep010 (halph : AlphabetComplete link07 alphabets) :
    ActualObstruction link07 FastDual07_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link07 rootCodes root_binding alphabets halph nonincident_complete
    FastDual07_010.pointList FastDual07_010.columns FastDual07_010.rows FastDual07_010.bound (by decide +kernel)
    FastDual07_010.column_mask FastDual07_010.checked hc F hF hroot hmin hout

theorem query494 (halph : AlphabetComplete link07 alphabets) : ActualObstruction link07 {8,9,10,11} := rep010 halph

def dualQuads : List (Finset Point) := [{3,6,7,8},{3,6,7,9},{3,6,7,10},{3,6,7,11},{3,6,8,9},{3,7,8,9},{3,6,8,10},{3,7,9,11},{3,6,8,11},{3,7,9,10},{3,6,9,10},{3,7,8,11},{3,6,9,11},{3,7,8,10},{3,6,10,11},{3,7,10,11},{6,7,8,9},{6,7,10,11},{8,9,10,11}]

theorem dual_actual (halph : AlphabetComplete link07 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link07 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query405 halph
  · exact query406 halph
  · exact query407 halph
  · exact query408 halph
  · exact query409 halph
  · exact query415 halph
  · exact query410 halph
  · exact query419 halph
  · exact query411 halph
  · exact query418 halph
  · exact query412 halph
  · exact query417 halph
  · exact query413 halph
  · exact query416 halph
  · exact query414 halph
  · exact query420 halph
  · exact query480 halph
  · exact query485 halph
  · exact query494 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link07 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link07 Q :=
  class_census link07 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source07
