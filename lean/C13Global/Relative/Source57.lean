import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source57
import C13Global.FastGroups.Source57Part00
import C13Global.FastGroups.Source57Part01
namespace C13.Global.Relative.Source57
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source57
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link57 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link57 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link57 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link57 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link57 alphabets) :
    ActualObstruction link57 FastDual57_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link57 rootCodes root_binding alphabets halph nonincident_complete
    FastDual57_000.pointList FastDual57_000.columns FastDual57_000.rows FastDual57_000.bound (by decide +kernel)
    FastDual57_000.column_mask FastDual57_000.checked hc F hF hroot hmin hout

theorem query296 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,3,5,10} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link57 = link57 :=
  root_symmetry_of_codes rootCodes link57 root_binding automorphism000 (by decide +kernel)

theorem query297 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,3,5,11} :=
  obstruction_transport link57 FastDual57_000.points {2,3,5,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

def automorphism001 : Equiv.Perm Point where
  toFun := ![9,8,10,11,4,5,7,6,1,0,2,3,12]
  invFun := ![9,8,10,11,4,5,7,6,1,0,2,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism001_hole : automorphism001 hole = hole := by decide +kernel

theorem automorphism001_root : transport automorphism001 link57 = link57 :=
  root_symmetry_of_codes rootCodes link57 root_binding automorphism001 (by decide +kernel)

theorem query348 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,5,10,11} :=
  obstruction_transport link57 FastDual57_000.points {2,5,10,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep000 halph)

def automorphism002 : Equiv.Perm Point where
  toFun := ![9,8,11,10,4,5,6,7,1,0,3,2,12]
  invFun := ![9,8,11,10,4,5,6,7,1,0,3,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism002_hole : automorphism002 hole = hole := by decide +kernel

theorem automorphism002_root : transport automorphism002 link57 = link57 :=
  root_symmetry_of_codes rootCodes link57 root_binding automorphism002 (by decide +kernel)

theorem query404 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {3,5,10,11} :=
  obstruction_transport link57 FastDual57_000.points {3,5,10,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link57 alphabets) :
    ActualObstruction link57 FastDual57_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link57 rootCodes root_binding alphabets halph nonincident_complete
    FastDual57_001.pointList FastDual57_001.columns FastDual57_001.rows FastDual57_001.bound (by decide +kernel)
    FastDual57_001.column_mask FastDual57_001.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,3,6,7} := rep001 halph

theorem query485 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {6,7,10,11} :=
  obstruction_transport link57 FastDual57_001.points {6,7,10,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link57 alphabets) :
    ActualObstruction link57 FastDual57_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link57 rootCodes root_binding alphabets halph nonincident_complete
    FastDual57_002.pointList FastDual57_002.columns FastDual57_002.rows FastDual57_002.bound (by decide +kernel)
    FastDual57_002.column_mask FastDual57_002.checked hc F hF hroot hmin hout

theorem query301 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,3,6,10} := rep002 halph

theorem query306 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,3,7,11} :=
  obstruction_transport link57 FastDual57_002.points {2,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem query364 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,7,10,11} :=
  obstruction_transport link57 FastDual57_002.points {2,7,10,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep002 halph)

theorem query414 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {3,6,10,11} :=
  obstruction_transport link57 FastDual57_002.points {3,6,10,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link57 alphabets) :
    ActualObstruction link57 FastDual57_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link57 rootCodes root_binding alphabets halph nonincident_complete
    FastDual57_003.pointList FastDual57_003.columns FastDual57_003.rows FastDual57_003.bound (by decide +kernel)
    FastDual57_003.column_mask FastDual57_003.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,3,6,11} := rep003 halph

theorem query305 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,3,7,10} :=
  obstruction_transport link57 FastDual57_003.points {2,3,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem query358 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,6,10,11} :=
  obstruction_transport link57 FastDual57_003.points {2,6,10,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep003 halph)

theorem query420 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {3,7,10,11} :=
  obstruction_transport link57 FastDual57_003.points {3,7,10,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link57 alphabets) :
    ActualObstruction link57 FastDual57_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link57 rootCodes root_binding alphabets halph nonincident_complete
    FastDual57_004.pointList FastDual57_004.columns FastDual57_004.rows FastDual57_004.bound (by decide +kernel)
    FastDual57_004.column_mask FastDual57_004.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,3,10,11} := rep004 halph

theorem rep005 (halph : AlphabetComplete link57 alphabets) :
    ActualObstruction link57 FastDual57_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link57 rootCodes root_binding alphabets halph nonincident_complete
    FastDual57_005.pointList FastDual57_005.columns FastDual57_005.rows FastDual57_005.bound (by decide +kernel)
    FastDual57_005.column_mask FastDual57_005.checked hc F hF hroot hmin hout

theorem query337 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,5,6,10} := rep005 halph

theorem query341 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,5,7,10} :=
  obstruction_transport link57 FastDual57_005.points {2,5,7,10} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep005 halph)

theorem query394 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {3,5,6,11} :=
  obstruction_transport link57 FastDual57_005.points {3,5,6,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep005 halph)

theorem query398 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {3,5,7,11} :=
  obstruction_transport link57 FastDual57_005.points {3,5,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link57 alphabets) :
    ActualObstruction link57 FastDual57_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link57 rootCodes root_binding alphabets halph nonincident_complete
    FastDual57_006.pointList FastDual57_006.columns FastDual57_006.rows FastDual57_006.bound (by decide +kernel)
    FastDual57_006.column_mask FastDual57_006.checked hc F hF hroot hmin hout

theorem query338 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,5,6,11} := rep006 halph

theorem query397 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {3,5,7,10} :=
  obstruction_transport link57 FastDual57_006.points {3,5,7,10} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link57 alphabets) :
    ActualObstruction link57 FastDual57_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link57 rootCodes root_binding alphabets halph nonincident_complete
    FastDual57_007.pointList FastDual57_007.columns FastDual57_007.rows FastDual57_007.bound (by decide +kernel)
    FastDual57_007.column_mask FastDual57_007.checked hc F hF hroot hmin hout

theorem query342 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,5,7,11} := rep007 halph

theorem query393 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {3,5,6,10} :=
  obstruction_transport link57 FastDual57_007.points {3,5,6,10} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link57 alphabets) :
    ActualObstruction link57 FastDual57_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link57 rootCodes root_binding alphabets halph nonincident_complete
    FastDual57_008.pointList FastDual57_008.columns FastDual57_008.rows FastDual57_008.bound (by decide +kernel)
    FastDual57_008.column_mask FastDual57_008.checked hc F hF hroot hmin hout

theorem query351 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,6,7,10} := rep008 halph

theorem query408 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {3,6,7,11} :=
  obstruction_transport link57 FastDual57_008.points {3,6,7,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link57 alphabets) :
    ActualObstruction link57 FastDual57_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link57 rootCodes root_binding alphabets halph nonincident_complete
    FastDual57_009.pointList FastDual57_009.columns FastDual57_009.rows FastDual57_009.bound (by decide +kernel)
    FastDual57_009.column_mask FastDual57_009.checked hc F hF hroot hmin hout

theorem query352 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {2,6,7,11} := rep009 halph

theorem query407 (halph : AlphabetComplete link57 alphabets) : ActualObstruction link57 {3,6,7,10} :=
  obstruction_transport link57 FastDual57_009.points {3,6,7,10} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep009 halph)

def dualQuads : List (Finset Point) := [{2,3,5,10},{2,3,5,11},{2,5,10,11},{3,5,10,11},{2,3,6,7},{6,7,10,11},{2,3,6,10},{2,3,7,11},{2,7,10,11},{3,6,10,11},{2,3,6,11},{2,3,7,10},{2,6,10,11},{3,7,10,11},{2,3,10,11},{2,5,6,10},{2,5,7,10},{3,5,6,11},{3,5,7,11},{2,5,6,11},{3,5,7,10},{2,5,7,11},{3,5,6,10},{2,6,7,10},{3,6,7,11},{2,6,7,11},{3,6,7,10}]

theorem dual_actual (halph : AlphabetComplete link57 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link57 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query296 halph
  · exact query297 halph
  · exact query348 halph
  · exact query404 halph
  · exact query298 halph
  · exact query485 halph
  · exact query301 halph
  · exact query306 halph
  · exact query364 halph
  · exact query414 halph
  · exact query302 halph
  · exact query305 halph
  · exact query358 halph
  · exact query420 halph
  · exact query312 halph
  · exact query337 halph
  · exact query341 halph
  · exact query394 halph
  · exact query398 halph
  · exact query338 halph
  · exact query397 halph
  · exact query342 halph
  · exact query393 halph
  · exact query351 halph
  · exact query408 halph
  · exact query352 halph
  · exact query407 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link57 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link57 Q :=
  class_census link57 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source57
