import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source16
import C13Global.FastGroups.Source16Part00
import C13Global.FastGroups.Source16Part01
namespace C13.Global.Relative.Source16
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source16
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link16 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link16 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link16 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link16 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link16 alphabets) :
    ActualObstruction link16 FastDual16_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link16 rootCodes root_binding alphabets halph nonincident_complete
    FastDual16_000.pointList FastDual16_000.columns FastDual16_000.rows FastDual16_000.bound (by decide +kernel)
    FastDual16_000.column_mask FastDual16_000.checked hc F hF hroot hmin hout

theorem query265 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {1,6,7,8} := rep000 halph

def symmetry266 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query266 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {1,6,7,9} :=
  obstruction_transport link16 FastDual16_000.points {1,6,7,9} symmetry266
    (by decide +kernel) (root_symmetry_of_codes rootCodes link16 root_binding symmetry266 (by decide +kernel)) (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link16 alphabets) :
    ActualObstruction link16 FastDual16_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link16 rootCodes root_binding alphabets halph nonincident_complete
    FastDual16_001.pointList FastDual16_001.columns FastDual16_001.rows FastDual16_001.bound (by decide +kernel)
    FastDual16_001.column_mask FastDual16_001.checked hc F hF hroot hmin hout

theorem query267 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {1,6,7,10} := rep001 halph

def symmetry268 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query268 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {1,6,7,11} :=
  obstruction_transport link16 FastDual16_001.points {1,6,7,11} symmetry268
    (by decide +kernel) (root_symmetry_of_codes rootCodes link16 root_binding symmetry268 (by decide +kernel)) (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link16 alphabets) :
    ActualObstruction link16 FastDual16_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link16 rootCodes root_binding alphabets halph nonincident_complete
    FastDual16_002.pointList FastDual16_002.columns FastDual16_002.rows FastDual16_002.bound (by decide +kernel)
    FastDual16_002.column_mask FastDual16_002.checked hc F hF hroot hmin hout

theorem query269 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {1,6,8,9} := rep002 halph

def symmetry275 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query275 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {1,7,8,9} :=
  obstruction_transport link16 FastDual16_002.points {1,7,8,9} symmetry275
    (by decide +kernel) (root_symmetry_of_codes rootCodes link16 root_binding symmetry275 (by decide +kernel)) (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link16 alphabets) :
    ActualObstruction link16 FastDual16_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link16 rootCodes root_binding alphabets halph nonincident_complete
    FastDual16_003.pointList FastDual16_003.columns FastDual16_003.rows FastDual16_003.bound (by decide +kernel)
    FastDual16_003.column_mask FastDual16_003.checked hc F hF hroot hmin hout

theorem query270 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {1,6,8,10} := rep003 halph

def symmetry279 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query279 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {1,7,9,11} :=
  obstruction_transport link16 FastDual16_003.points {1,7,9,11} symmetry279
    (by decide +kernel) (root_symmetry_of_codes rootCodes link16 root_binding symmetry279 (by decide +kernel)) (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link16 alphabets) :
    ActualObstruction link16 FastDual16_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link16 rootCodes root_binding alphabets halph nonincident_complete
    FastDual16_004.pointList FastDual16_004.columns FastDual16_004.rows FastDual16_004.bound (by decide +kernel)
    FastDual16_004.column_mask FastDual16_004.checked hc F hF hroot hmin hout

theorem query271 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {1,6,8,11} := rep004 halph

def symmetry278 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query278 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {1,7,9,10} :=
  obstruction_transport link16 FastDual16_004.points {1,7,9,10} symmetry278
    (by decide +kernel) (root_symmetry_of_codes rootCodes link16 root_binding symmetry278 (by decide +kernel)) (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link16 alphabets) :
    ActualObstruction link16 FastDual16_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link16 rootCodes root_binding alphabets halph nonincident_complete
    FastDual16_005.pointList FastDual16_005.columns FastDual16_005.rows FastDual16_005.bound (by decide +kernel)
    FastDual16_005.column_mask FastDual16_005.checked hc F hF hroot hmin hout

theorem query272 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {1,6,9,10} := rep005 halph

def symmetry277 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query277 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {1,7,8,11} :=
  obstruction_transport link16 FastDual16_005.points {1,7,8,11} symmetry277
    (by decide +kernel) (root_symmetry_of_codes rootCodes link16 root_binding symmetry277 (by decide +kernel)) (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link16 alphabets) :
    ActualObstruction link16 FastDual16_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link16 rootCodes root_binding alphabets halph nonincident_complete
    FastDual16_006.pointList FastDual16_006.columns FastDual16_006.rows FastDual16_006.bound (by decide +kernel)
    FastDual16_006.column_mask FastDual16_006.checked hc F hF hroot hmin hout

theorem query273 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {1,6,9,11} := rep006 halph

def symmetry276 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query276 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {1,7,8,10} :=
  obstruction_transport link16 FastDual16_006.points {1,7,8,10} symmetry276
    (by decide +kernel) (root_symmetry_of_codes rootCodes link16 root_binding symmetry276 (by decide +kernel)) (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link16 alphabets) :
    ActualObstruction link16 FastDual16_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link16 rootCodes root_binding alphabets halph nonincident_complete
    FastDual16_007.pointList FastDual16_007.columns FastDual16_007.rows FastDual16_007.bound (by decide +kernel)
    FastDual16_007.column_mask FastDual16_007.checked hc F hF hroot hmin hout

theorem query274 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {1,6,10,11} := rep007 halph

def symmetry280 : Equiv.Perm Point where
  toFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  invFun := ![0,1,2,3,5,4,7,6,9,8,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem query280 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {1,7,10,11} :=
  obstruction_transport link16 FastDual16_007.points {1,7,10,11} symmetry280
    (by decide +kernel) (root_symmetry_of_codes rootCodes link16 root_binding symmetry280 (by decide +kernel)) (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link16 alphabets) :
    ActualObstruction link16 FastDual16_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link16 rootCodes root_binding alphabets halph nonincident_complete
    FastDual16_008.pointList FastDual16_008.columns FastDual16_008.rows FastDual16_008.bound (by decide +kernel)
    FastDual16_008.column_mask FastDual16_008.checked hc F hF hroot hmin hout

theorem query480 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {6,7,8,9} := rep008 halph

theorem rep009 (halph : AlphabetComplete link16 alphabets) :
    ActualObstruction link16 FastDual16_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link16 rootCodes root_binding alphabets halph nonincident_complete
    FastDual16_009.pointList FastDual16_009.columns FastDual16_009.rows FastDual16_009.bound (by decide +kernel)
    FastDual16_009.column_mask FastDual16_009.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {6,7,10,11} := rep009 halph

theorem rep010 (halph : AlphabetComplete link16 alphabets) :
    ActualObstruction link16 FastDual16_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link16 rootCodes root_binding alphabets halph nonincident_complete
    FastDual16_010.pointList FastDual16_010.columns FastDual16_010.rows FastDual16_010.bound (by decide +kernel)
    FastDual16_010.column_mask FastDual16_010.checked hc F hF hroot hmin hout

theorem query494 (halph : AlphabetComplete link16 alphabets) : ActualObstruction link16 {8,9,10,11} := rep010 halph

def dualQuads : List (Finset Point) := [{1,6,7,8},{1,6,7,9},{1,6,7,10},{1,6,7,11},{1,6,8,9},{1,7,8,9},{1,6,8,10},{1,7,9,11},{1,6,8,11},{1,7,9,10},{1,6,9,10},{1,7,8,11},{1,6,9,11},{1,7,8,10},{1,6,10,11},{1,7,10,11},{6,7,8,9},{6,7,10,11},{8,9,10,11}]

theorem dual_actual (halph : AlphabetComplete link16 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link16 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query265 halph
  · exact query266 halph
  · exact query267 halph
  · exact query268 halph
  · exact query269 halph
  · exact query275 halph
  · exact query270 halph
  · exact query279 halph
  · exact query271 halph
  · exact query278 halph
  · exact query272 halph
  · exact query277 halph
  · exact query273 halph
  · exact query276 halph
  · exact query274 halph
  · exact query280 halph
  · exact query480 halph
  · exact query485 halph
  · exact query494 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link16 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link16 Q :=
  class_census link16 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source16
