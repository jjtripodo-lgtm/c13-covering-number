import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source30
import C13Global.FastGroups.Source30Part00
import C13Global.FastGroups.Source30Part01
namespace C13.Global.Relative.Source30
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source30
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link30 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link30 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link30 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link30 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link30 alphabets) :
    ActualObstruction link30 FastDual30_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link30 rootCodes root_binding alphabets halph nonincident_complete
    FastDual30_000.pointList FastDual30_000.columns FastDual30_000.rows FastDual30_000.bound (by decide +kernel)
    FastDual30_000.column_mask FastDual30_000.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,3,6,7} := rep000 halph

theorem rep001 (halph : AlphabetComplete link30 alphabets) :
    ActualObstruction link30 FastDual30_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link30 rootCodes root_binding alphabets halph nonincident_complete
    FastDual30_001.pointList FastDual30_001.columns FastDual30_001.rows FastDual30_001.bound (by decide +kernel)
    FastDual30_001.column_mask FastDual30_001.checked hc F hF hroot hmin hout

theorem query300 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,3,6,9} := rep001 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link30 = link30 :=
  root_symmetry_of_codes rootCodes link30 root_binding automorphism000 (by decide +kernel)

theorem query304 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,3,7,9} :=
  obstruction_transport link30 FastDual30_001.points {2,3,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link30 alphabets) :
    ActualObstruction link30 FastDual30_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link30 rootCodes root_binding alphabets halph nonincident_complete
    FastDual30_002.pointList FastDual30_002.columns FastDual30_002.rows FastDual30_002.bound (by decide +kernel)
    FastDual30_002.column_mask FastDual30_002.checked hc F hF hroot hmin hout

theorem query301 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,3,6,10} := rep002 halph

theorem query306 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,3,7,11} :=
  obstruction_transport link30 FastDual30_002.points {2,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link30 alphabets) :
    ActualObstruction link30 FastDual30_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link30 rootCodes root_binding alphabets halph nonincident_complete
    FastDual30_003.pointList FastDual30_003.columns FastDual30_003.rows FastDual30_003.bound (by decide +kernel)
    FastDual30_003.column_mask FastDual30_003.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,3,6,11} := rep003 halph

theorem query305 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,3,7,10} :=
  obstruction_transport link30 FastDual30_003.points {2,3,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link30 alphabets) :
    ActualObstruction link30 FastDual30_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link30 rootCodes root_binding alphabets halph nonincident_complete
    FastDual30_004.pointList FastDual30_004.columns FastDual30_004.rows FastDual30_004.bound (by decide +kernel)
    FastDual30_004.column_mask FastDual30_004.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,3,10,11} := rep004 halph

theorem rep005 (halph : AlphabetComplete link30 alphabets) :
    ActualObstruction link30 FastDual30_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link30 rootCodes root_binding alphabets halph nonincident_complete
    FastDual30_005.pointList FastDual30_005.columns FastDual30_005.rows FastDual30_005.bound (by decide +kernel)
    FastDual30_005.column_mask FastDual30_005.checked hc F hF hroot hmin hout

theorem query350 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,6,7,9} := rep005 halph

theorem query406 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {3,6,7,9} :=
  obstruction_transport link30 FastDual30_005.points {3,6,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link30 alphabets) :
    ActualObstruction link30 FastDual30_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link30 rootCodes root_binding alphabets halph nonincident_complete
    FastDual30_006.pointList FastDual30_006.columns FastDual30_006.rows FastDual30_006.bound (by decide +kernel)
    FastDual30_006.column_mask FastDual30_006.checked hc F hF hroot hmin hout

theorem query351 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,6,7,10} := rep006 halph

theorem query408 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {3,6,7,11} :=
  obstruction_transport link30 FastDual30_006.points {3,6,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link30 alphabets) :
    ActualObstruction link30 FastDual30_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link30 rootCodes root_binding alphabets halph nonincident_complete
    FastDual30_007.pointList FastDual30_007.columns FastDual30_007.rows FastDual30_007.bound (by decide +kernel)
    FastDual30_007.column_mask FastDual30_007.checked hc F hF hroot hmin hout

theorem query352 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,6,7,11} := rep007 halph

theorem query407 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {3,6,7,10} :=
  obstruction_transport link30 FastDual30_007.points {3,6,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link30 alphabets) :
    ActualObstruction link30 FastDual30_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link30 rootCodes root_binding alphabets halph nonincident_complete
    FastDual30_008.pointList FastDual30_008.columns FastDual30_008.rows FastDual30_008.bound (by decide +kernel)
    FastDual30_008.column_mask FastDual30_008.checked hc F hF hroot hmin hout

theorem query356 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,6,9,10} := rep008 halph

theorem query419 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {3,7,9,11} :=
  obstruction_transport link30 FastDual30_008.points {3,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link30 alphabets) :
    ActualObstruction link30 FastDual30_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link30 rootCodes root_binding alphabets halph nonincident_complete
    FastDual30_009.pointList FastDual30_009.columns FastDual30_009.rows FastDual30_009.bound (by decide +kernel)
    FastDual30_009.column_mask FastDual30_009.checked hc F hF hroot hmin hout

theorem query357 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,6,9,11} := rep009 halph

theorem query418 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {3,7,9,10} :=
  obstruction_transport link30 FastDual30_009.points {3,7,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link30 alphabets) :
    ActualObstruction link30 FastDual30_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link30 rootCodes root_binding alphabets halph nonincident_complete
    FastDual30_010.pointList FastDual30_010.columns FastDual30_010.rows FastDual30_010.bound (by decide +kernel)
    FastDual30_010.column_mask FastDual30_010.checked hc F hF hroot hmin hout

theorem query358 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,6,10,11} := rep010 halph

theorem query420 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {3,7,10,11} :=
  obstruction_transport link30 FastDual30_010.points {3,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link30 alphabets) :
    ActualObstruction link30 FastDual30_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link30 rootCodes root_binding alphabets halph nonincident_complete
    FastDual30_011.pointList FastDual30_011.columns FastDual30_011.rows FastDual30_011.bound (by decide +kernel)
    FastDual30_011.column_mask FastDual30_011.checked hc F hF hroot hmin hout

theorem query362 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,7,9,10} := rep011 halph

theorem query413 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {3,6,9,11} :=
  obstruction_transport link30 FastDual30_011.points {3,6,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link30 alphabets) :
    ActualObstruction link30 FastDual30_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link30 rootCodes root_binding alphabets halph nonincident_complete
    FastDual30_012.pointList FastDual30_012.columns FastDual30_012.rows FastDual30_012.bound (by decide +kernel)
    FastDual30_012.column_mask FastDual30_012.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,7,9,11} := rep012 halph

theorem query412 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {3,6,9,10} :=
  obstruction_transport link30 FastDual30_012.points {3,6,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep012 halph)

theorem rep013 (halph : AlphabetComplete link30 alphabets) :
    ActualObstruction link30 FastDual30_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link30 rootCodes root_binding alphabets halph nonincident_complete
    FastDual30_013.pointList FastDual30_013.columns FastDual30_013.rows FastDual30_013.bound (by decide +kernel)
    FastDual30_013.column_mask FastDual30_013.checked hc F hF hroot hmin hout

theorem query364 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {2,7,10,11} := rep013 halph

theorem query414 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {3,6,10,11} :=
  obstruction_transport link30 FastDual30_013.points {3,6,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep013 halph)

theorem rep014 (halph : AlphabetComplete link30 alphabets) :
    ActualObstruction link30 FastDual30_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link30 rootCodes root_binding alphabets halph nonincident_complete
    FastDual30_014.pointList FastDual30_014.columns FastDual30_014.rows FastDual30_014.bound (by decide +kernel)
    FastDual30_014.column_mask FastDual30_014.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link30 alphabets) : ActualObstruction link30 {6,7,10,11} := rep014 halph

def dualQuads : List (Finset Point) := [{2,3,6,7},{2,3,6,9},{2,3,7,9},{2,3,6,10},{2,3,7,11},{2,3,6,11},{2,3,7,10},{2,3,10,11},{2,6,7,9},{3,6,7,9},{2,6,7,10},{3,6,7,11},{2,6,7,11},{3,6,7,10},{2,6,9,10},{3,7,9,11},{2,6,9,11},{3,7,9,10},{2,6,10,11},{3,7,10,11},{2,7,9,10},{3,6,9,11},{2,7,9,11},{3,6,9,10},{2,7,10,11},{3,6,10,11},{6,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link30 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link30 Q := by
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

theorem all_foursets (halph : AlphabetComplete link30 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link30 Q :=
  class_census link30 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source30
