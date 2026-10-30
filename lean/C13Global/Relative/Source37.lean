import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source37
import C13Global.FastGroups.Source37Part00
import C13Global.FastGroups.Source37Part01
namespace C13.Global.Relative.Source37
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source37
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link37 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link37 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link37 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link37 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link37 alphabets) :
    ActualObstruction link37 FastDual37_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link37 rootCodes root_binding alphabets halph nonincident_complete
    FastDual37_000.pointList FastDual37_000.columns FastDual37_000.rows FastDual37_000.bound (by decide +kernel)
    FastDual37_000.column_mask FastDual37_000.checked hc F hF hroot hmin hout

theorem query192 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {1,2,7,9} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![8,10,9,11,4,6,5,7,0,2,1,3,12]
  invFun := ![8,10,9,11,4,6,5,7,0,2,1,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link37 = link37 :=
  root_symmetry_of_codes rootCodes link37 root_binding automorphism000 (by decide +kernel)

theorem query362 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {2,7,9,10} :=
  obstruction_transport link37 FastDual37_000.points {2,7,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link37 alphabets) :
    ActualObstruction link37 FastDual37_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link37 rootCodes root_binding alphabets halph nonincident_complete
    FastDual37_001.pointList FastDual37_001.columns FastDual37_001.rows FastDual37_001.bound (by decide +kernel)
    FastDual37_001.column_mask FastDual37_001.checked hc F hF hroot hmin hout

theorem query193 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {1,2,7,10} := rep001 halph

theorem query278 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {1,7,9,10} :=
  obstruction_transport link37 FastDual37_001.points {1,7,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link37 alphabets) :
    ActualObstruction link37 FastDual37_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link37 rootCodes root_binding alphabets halph nonincident_complete
    FastDual37_002.pointList FastDual37_002.columns FastDual37_002.rows FastDual37_002.bound (by decide +kernel)
    FastDual37_002.column_mask FastDual37_002.checked hc F hF hroot hmin hout

theorem query194 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {1,2,7,11} := rep002 halph

theorem query418 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {3,7,9,10} :=
  obstruction_transport link37 FastDual37_002.points {3,7,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link37 alphabets) :
    ActualObstruction link37 FastDual37_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link37 rootCodes root_binding alphabets halph nonincident_complete
    FastDual37_003.pointList FastDual37_003.columns FastDual37_003.rows FastDual37_003.bound (by decide +kernel)
    FastDual37_003.column_mask FastDual37_003.checked hc F hF hroot hmin hout

theorem query198 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {1,2,9,10} := rep003 halph

theorem rep004 (halph : AlphabetComplete link37 alphabets) :
    ActualObstruction link37 FastDual37_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link37 rootCodes root_binding alphabets halph nonincident_complete
    FastDual37_004.pointList FastDual37_004.columns FastDual37_004.rows FastDual37_004.bound (by decide +kernel)
    FastDual37_004.column_mask FastDual37_004.checked hc F hF hroot hmin hout

theorem query220 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {1,3,7,9} := rep004 halph

theorem query364 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {2,7,10,11} :=
  obstruction_transport link37 FastDual37_004.points {2,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link37 alphabets) :
    ActualObstruction link37 FastDual37_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link37 rootCodes root_binding alphabets halph nonincident_complete
    FastDual37_005.pointList FastDual37_005.columns FastDual37_005.rows FastDual37_005.bound (by decide +kernel)
    FastDual37_005.column_mask FastDual37_005.checked hc F hF hroot hmin hout

theorem query221 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {1,3,7,10} := rep005 halph

theorem query280 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {1,7,10,11} :=
  obstruction_transport link37 FastDual37_005.points {1,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link37 alphabets) :
    ActualObstruction link37 FastDual37_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link37 rootCodes root_binding alphabets halph nonincident_complete
    FastDual37_006.pointList FastDual37_006.columns FastDual37_006.rows FastDual37_006.bound (by decide +kernel)
    FastDual37_006.column_mask FastDual37_006.checked hc F hF hroot hmin hout

theorem query222 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {1,3,7,11} := rep006 halph

theorem query420 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {3,7,10,11} :=
  obstruction_transport link37 FastDual37_006.points {3,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link37 alphabets) :
    ActualObstruction link37 FastDual37_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link37 rootCodes root_binding alphabets halph nonincident_complete
    FastDual37_007.pointList FastDual37_007.columns FastDual37_007.rows FastDual37_007.bound (by decide +kernel)
    FastDual37_007.column_mask FastDual37_007.checked hc F hF hroot hmin hout

theorem query227 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {1,3,9,11} := rep007 halph

theorem query312 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {2,3,10,11} :=
  obstruction_transport link37 FastDual37_007.points {2,3,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link37 alphabets) :
    ActualObstruction link37 FastDual37_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link37 rootCodes root_binding alphabets halph nonincident_complete
    FastDual37_008.pointList FastDual37_008.columns FastDual37_008.rows FastDual37_008.bound (by decide +kernel)
    FastDual37_008.column_mask FastDual37_008.checked hc F hF hroot hmin hout

theorem query279 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {1,7,9,11} := rep008 halph

theorem query305 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {2,3,7,10} :=
  obstruction_transport link37 FastDual37_008.points {2,3,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link37 alphabets) :
    ActualObstruction link37 FastDual37_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link37 rootCodes root_binding alphabets halph nonincident_complete
    FastDual37_009.pointList FastDual37_009.columns FastDual37_009.rows FastDual37_009.bound (by decide +kernel)
    FastDual37_009.column_mask FastDual37_009.checked hc F hF hroot hmin hout

theorem query304 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {2,3,7,9} := rep009 halph

theorem query363 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {2,7,9,11} :=
  obstruction_transport link37 FastDual37_009.points {2,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link37 alphabets) :
    ActualObstruction link37 FastDual37_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link37 rootCodes root_binding alphabets halph nonincident_complete
    FastDual37_010.pointList FastDual37_010.columns FastDual37_010.rows FastDual37_010.bound (by decide +kernel)
    FastDual37_010.column_mask FastDual37_010.checked hc F hF hroot hmin hout

theorem query306 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {2,3,7,11} := rep010 halph

theorem query419 (halph : AlphabetComplete link37 alphabets) : ActualObstruction link37 {3,7,9,11} :=
  obstruction_transport link37 FastDual37_010.points {3,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep010 halph)

def dualQuads : List (Finset Point) := [{1,2,7,9},{2,7,9,10},{1,2,7,10},{1,7,9,10},{1,2,7,11},{3,7,9,10},{1,2,9,10},{1,3,7,9},{2,7,10,11},{1,3,7,10},{1,7,10,11},{1,3,7,11},{3,7,10,11},{1,3,9,11},{2,3,10,11},{1,7,9,11},{2,3,7,10},{2,3,7,9},{2,7,9,11},{2,3,7,11},{3,7,9,11}]

theorem dual_actual (halph : AlphabetComplete link37 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link37 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query192 halph
  · exact query362 halph
  · exact query193 halph
  · exact query278 halph
  · exact query194 halph
  · exact query418 halph
  · exact query198 halph
  · exact query220 halph
  · exact query364 halph
  · exact query221 halph
  · exact query280 halph
  · exact query222 halph
  · exact query420 halph
  · exact query227 halph
  · exact query312 halph
  · exact query279 halph
  · exact query305 halph
  · exact query304 halph
  · exact query363 halph
  · exact query306 halph
  · exact query419 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link37 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link37 Q :=
  class_census link37 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source37
