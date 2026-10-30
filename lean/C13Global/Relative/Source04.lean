import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source04
import C13Global.FastGroups.Source04Part00
import C13Global.FastGroups.Source04Part01
namespace C13.Global.Relative.Source04
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source04
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link04 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link04 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link04 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link04 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link04 alphabets) :
    ActualObstruction link04 FastDual04_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link04 rootCodes root_binding alphabets halph nonincident_complete
    FastDual04_000.pointList FastDual04_000.columns FastDual04_000.rows FastDual04_000.bound (by decide +kernel)
    FastDual04_000.column_mask FastDual04_000.checked hc F hF hroot hmin hout

theorem query303 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {2,3,7,8} := rep000 halph

def symmetry304 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query304 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {2,3,7,9} :=
  obstruction_transport link04 FastDual04_000.points {2,3,7,9} symmetry304
    (by decide +kernel) (root_symmetry_of_codes rootCodes link04 root_binding symmetry304 (by decide +kernel)) (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link04 alphabets) :
    ActualObstruction link04 FastDual04_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link04 rootCodes root_binding alphabets halph nonincident_complete
    FastDual04_001.pointList FastDual04_001.columns FastDual04_001.rows FastDual04_001.bound (by decide +kernel)
    FastDual04_001.column_mask FastDual04_001.checked hc F hF hroot hmin hout

theorem query305 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {2,3,7,10} := rep001 halph

theorem rep002 (halph : AlphabetComplete link04 alphabets) :
    ActualObstruction link04 FastDual04_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link04 rootCodes root_binding alphabets halph nonincident_complete
    FastDual04_002.pointList FastDual04_002.columns FastDual04_002.rows FastDual04_002.bound (by decide +kernel)
    FastDual04_002.column_mask FastDual04_002.checked hc F hF hroot hmin hout

theorem query306 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {2,3,7,11} := rep002 halph

theorem rep003 (halph : AlphabetComplete link04 alphabets) :
    ActualObstruction link04 FastDual04_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link04 rootCodes root_binding alphabets halph nonincident_complete
    FastDual04_003.pointList FastDual04_003.columns FastDual04_003.rows FastDual04_003.bound (by decide +kernel)
    FastDual04_003.column_mask FastDual04_003.checked hc F hF hroot hmin hout

theorem query307 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {2,3,8,9} := rep003 halph

theorem rep004 (halph : AlphabetComplete link04 alphabets) :
    ActualObstruction link04 FastDual04_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link04 rootCodes root_binding alphabets halph nonincident_complete
    FastDual04_004.pointList FastDual04_004.columns FastDual04_004.rows FastDual04_004.bound (by decide +kernel)
    FastDual04_004.column_mask FastDual04_004.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {2,3,10,11} := rep004 halph

theorem rep005 (halph : AlphabetComplete link04 alphabets) :
    ActualObstruction link04 FastDual04_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link04 rootCodes root_binding alphabets halph nonincident_complete
    FastDual04_005.pointList FastDual04_005.columns FastDual04_005.rows FastDual04_005.bound (by decide +kernel)
    FastDual04_005.column_mask FastDual04_005.checked hc F hF hroot hmin hout

theorem query359 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {2,7,8,9} := rep005 halph

def symmetry415 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query415 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {3,7,8,9} :=
  obstruction_transport link04 FastDual04_005.points {3,7,8,9} symmetry415
    (by decide +kernel) (root_symmetry_of_codes rootCodes link04 root_binding symmetry415 (by decide +kernel)) (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link04 alphabets) :
    ActualObstruction link04 FastDual04_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link04 rootCodes root_binding alphabets halph nonincident_complete
    FastDual04_006.pointList FastDual04_006.columns FastDual04_006.rows FastDual04_006.bound (by decide +kernel)
    FastDual04_006.column_mask FastDual04_006.checked hc F hF hroot hmin hout

theorem query360 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {2,7,8,10} := rep006 halph

def symmetry418 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query418 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {3,7,9,10} :=
  obstruction_transport link04 FastDual04_006.points {3,7,9,10} symmetry418
    (by decide +kernel) (root_symmetry_of_codes rootCodes link04 root_binding symmetry418 (by decide +kernel)) (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link04 alphabets) :
    ActualObstruction link04 FastDual04_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link04 rootCodes root_binding alphabets halph nonincident_complete
    FastDual04_007.pointList FastDual04_007.columns FastDual04_007.rows FastDual04_007.bound (by decide +kernel)
    FastDual04_007.column_mask FastDual04_007.checked hc F hF hroot hmin hout

theorem query361 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {2,7,8,11} := rep007 halph

def symmetry419 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query419 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {3,7,9,11} :=
  obstruction_transport link04 FastDual04_007.points {3,7,9,11} symmetry419
    (by decide +kernel) (root_symmetry_of_codes rootCodes link04 root_binding symmetry419 (by decide +kernel)) (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link04 alphabets) :
    ActualObstruction link04 FastDual04_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link04 rootCodes root_binding alphabets halph nonincident_complete
    FastDual04_008.pointList FastDual04_008.columns FastDual04_008.rows FastDual04_008.bound (by decide +kernel)
    FastDual04_008.column_mask FastDual04_008.checked hc F hF hroot hmin hout

theorem query362 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {2,7,9,10} := rep008 halph

def symmetry416 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query416 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {3,7,8,10} :=
  obstruction_transport link04 FastDual04_008.points {3,7,8,10} symmetry416
    (by decide +kernel) (root_symmetry_of_codes rootCodes link04 root_binding symmetry416 (by decide +kernel)) (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link04 alphabets) :
    ActualObstruction link04 FastDual04_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link04 rootCodes root_binding alphabets halph nonincident_complete
    FastDual04_009.pointList FastDual04_009.columns FastDual04_009.rows FastDual04_009.bound (by decide +kernel)
    FastDual04_009.column_mask FastDual04_009.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {2,7,9,11} := rep009 halph

def symmetry417 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query417 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {3,7,8,11} :=
  obstruction_transport link04 FastDual04_009.points {3,7,8,11} symmetry417
    (by decide +kernel) (root_symmetry_of_codes rootCodes link04 root_binding symmetry417 (by decide +kernel)) (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link04 alphabets) :
    ActualObstruction link04 FastDual04_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link04 rootCodes root_binding alphabets halph nonincident_complete
    FastDual04_010.pointList FastDual04_010.columns FastDual04_010.rows FastDual04_010.bound (by decide +kernel)
    FastDual04_010.column_mask FastDual04_010.checked hc F hF hroot hmin hout

theorem query364 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {2,7,10,11} := rep010 halph

def symmetry420 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query420 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {3,7,10,11} :=
  obstruction_transport link04 FastDual04_010.points {3,7,10,11} symmetry420
    (by decide +kernel) (root_symmetry_of_codes rootCodes link04 root_binding symmetry420 (by decide +kernel)) (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link04 alphabets) :
    ActualObstruction link04 FastDual04_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link04 rootCodes root_binding alphabets halph nonincident_complete
    FastDual04_011.pointList FastDual04_011.columns FastDual04_011.rows FastDual04_011.bound (by decide +kernel)
    FastDual04_011.column_mask FastDual04_011.checked hc F hF hroot hmin hout

theorem query494 (halph : AlphabetComplete link04 alphabets) : ActualObstruction link04 {8,9,10,11} := rep011 halph

def dualQuads : List (Finset Point) := [{2,3,7,8},{2,3,7,9},{2,3,7,10},{2,3,7,11},{2,3,8,9},{2,3,10,11},{2,7,8,9},{3,7,8,9},{2,7,8,10},{3,7,9,10},{2,7,8,11},{3,7,9,11},{2,7,9,10},{3,7,8,10},{2,7,9,11},{3,7,8,11},{2,7,10,11},{3,7,10,11},{8,9,10,11}]

theorem dual_actual (halph : AlphabetComplete link04 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link04 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query303 halph
  · exact query304 halph
  · exact query305 halph
  · exact query306 halph
  · exact query307 halph
  · exact query312 halph
  · exact query359 halph
  · exact query415 halph
  · exact query360 halph
  · exact query418 halph
  · exact query361 halph
  · exact query419 halph
  · exact query362 halph
  · exact query416 halph
  · exact query363 halph
  · exact query417 halph
  · exact query364 halph
  · exact query420 halph
  · exact query494 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link04 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link04 Q :=
  class_census link04 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source04
