import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source29
import C13Global.FastGroups.Source29Part00
import C13Global.FastGroups.Source29Part01
namespace C13.Global.Relative.Source29
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source29
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link29 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link29 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link29 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link29 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link29 alphabets) :
    ActualObstruction link29 FastDual29_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link29 rootCodes root_binding alphabets halph nonincident_complete
    FastDual29_000.pointList FastDual29_000.columns FastDual29_000.rows FastDual29_000.bound (by decide +kernel)
    FastDual29_000.column_mask FastDual29_000.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,3,6,7} := rep000 halph

theorem rep001 (halph : AlphabetComplete link29 alphabets) :
    ActualObstruction link29 FastDual29_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link29 rootCodes root_binding alphabets halph nonincident_complete
    FastDual29_001.pointList FastDual29_001.columns FastDual29_001.rows FastDual29_001.bound (by decide +kernel)
    FastDual29_001.column_mask FastDual29_001.checked hc F hF hroot hmin hout

theorem query300 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,3,6,9} := rep001 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link29 = link29 :=
  root_symmetry_of_codes rootCodes link29 root_binding automorphism000 (by decide +kernel)

theorem query304 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,3,7,9} :=
  obstruction_transport link29 FastDual29_001.points {2,3,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link29 alphabets) :
    ActualObstruction link29 FastDual29_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link29 rootCodes root_binding alphabets halph nonincident_complete
    FastDual29_002.pointList FastDual29_002.columns FastDual29_002.rows FastDual29_002.bound (by decide +kernel)
    FastDual29_002.column_mask FastDual29_002.checked hc F hF hroot hmin hout

theorem query301 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,3,6,10} := rep002 halph

theorem query306 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,3,7,11} :=
  obstruction_transport link29 FastDual29_002.points {2,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link29 alphabets) :
    ActualObstruction link29 FastDual29_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link29 rootCodes root_binding alphabets halph nonincident_complete
    FastDual29_003.pointList FastDual29_003.columns FastDual29_003.rows FastDual29_003.bound (by decide +kernel)
    FastDual29_003.column_mask FastDual29_003.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,3,6,11} := rep003 halph

theorem query305 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,3,7,10} :=
  obstruction_transport link29 FastDual29_003.points {2,3,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link29 alphabets) :
    ActualObstruction link29 FastDual29_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link29 rootCodes root_binding alphabets halph nonincident_complete
    FastDual29_004.pointList FastDual29_004.columns FastDual29_004.rows FastDual29_004.bound (by decide +kernel)
    FastDual29_004.column_mask FastDual29_004.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,3,10,11} := rep004 halph

theorem rep005 (halph : AlphabetComplete link29 alphabets) :
    ActualObstruction link29 FastDual29_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link29 rootCodes root_binding alphabets halph nonincident_complete
    FastDual29_005.pointList FastDual29_005.columns FastDual29_005.rows FastDual29_005.bound (by decide +kernel)
    FastDual29_005.column_mask FastDual29_005.checked hc F hF hroot hmin hout

theorem query350 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,6,7,9} := rep005 halph

theorem query406 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {3,6,7,9} :=
  obstruction_transport link29 FastDual29_005.points {3,6,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link29 alphabets) :
    ActualObstruction link29 FastDual29_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link29 rootCodes root_binding alphabets halph nonincident_complete
    FastDual29_006.pointList FastDual29_006.columns FastDual29_006.rows FastDual29_006.bound (by decide +kernel)
    FastDual29_006.column_mask FastDual29_006.checked hc F hF hroot hmin hout

theorem query351 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,6,7,10} := rep006 halph

theorem query408 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {3,6,7,11} :=
  obstruction_transport link29 FastDual29_006.points {3,6,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link29 alphabets) :
    ActualObstruction link29 FastDual29_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link29 rootCodes root_binding alphabets halph nonincident_complete
    FastDual29_007.pointList FastDual29_007.columns FastDual29_007.rows FastDual29_007.bound (by decide +kernel)
    FastDual29_007.column_mask FastDual29_007.checked hc F hF hroot hmin hout

theorem query352 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,6,7,11} := rep007 halph

theorem query407 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {3,6,7,10} :=
  obstruction_transport link29 FastDual29_007.points {3,6,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link29 alphabets) :
    ActualObstruction link29 FastDual29_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link29 rootCodes root_binding alphabets halph nonincident_complete
    FastDual29_008.pointList FastDual29_008.columns FastDual29_008.rows FastDual29_008.bound (by decide +kernel)
    FastDual29_008.column_mask FastDual29_008.checked hc F hF hroot hmin hout

theorem query356 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,6,9,10} := rep008 halph

theorem query419 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {3,7,9,11} :=
  obstruction_transport link29 FastDual29_008.points {3,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link29 alphabets) :
    ActualObstruction link29 FastDual29_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link29 rootCodes root_binding alphabets halph nonincident_complete
    FastDual29_009.pointList FastDual29_009.columns FastDual29_009.rows FastDual29_009.bound (by decide +kernel)
    FastDual29_009.column_mask FastDual29_009.checked hc F hF hroot hmin hout

theorem query357 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,6,9,11} := rep009 halph

theorem query418 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {3,7,9,10} :=
  obstruction_transport link29 FastDual29_009.points {3,7,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link29 alphabets) :
    ActualObstruction link29 FastDual29_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link29 rootCodes root_binding alphabets halph nonincident_complete
    FastDual29_010.pointList FastDual29_010.columns FastDual29_010.rows FastDual29_010.bound (by decide +kernel)
    FastDual29_010.column_mask FastDual29_010.checked hc F hF hroot hmin hout

theorem query358 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,6,10,11} := rep010 halph

theorem query420 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {3,7,10,11} :=
  obstruction_transport link29 FastDual29_010.points {3,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link29 alphabets) :
    ActualObstruction link29 FastDual29_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link29 rootCodes root_binding alphabets halph nonincident_complete
    FastDual29_011.pointList FastDual29_011.columns FastDual29_011.rows FastDual29_011.bound (by decide +kernel)
    FastDual29_011.column_mask FastDual29_011.checked hc F hF hroot hmin hout

theorem query362 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,7,9,10} := rep011 halph

theorem query413 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {3,6,9,11} :=
  obstruction_transport link29 FastDual29_011.points {3,6,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link29 alphabets) :
    ActualObstruction link29 FastDual29_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link29 rootCodes root_binding alphabets halph nonincident_complete
    FastDual29_012.pointList FastDual29_012.columns FastDual29_012.rows FastDual29_012.bound (by decide +kernel)
    FastDual29_012.column_mask FastDual29_012.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,7,9,11} := rep012 halph

theorem query412 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {3,6,9,10} :=
  obstruction_transport link29 FastDual29_012.points {3,6,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep012 halph)

theorem rep013 (halph : AlphabetComplete link29 alphabets) :
    ActualObstruction link29 FastDual29_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link29 rootCodes root_binding alphabets halph nonincident_complete
    FastDual29_013.pointList FastDual29_013.columns FastDual29_013.rows FastDual29_013.bound (by decide +kernel)
    FastDual29_013.column_mask FastDual29_013.checked hc F hF hroot hmin hout

theorem query364 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {2,7,10,11} := rep013 halph

theorem query414 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {3,6,10,11} :=
  obstruction_transport link29 FastDual29_013.points {3,6,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep013 halph)

theorem rep014 (halph : AlphabetComplete link29 alphabets) :
    ActualObstruction link29 FastDual29_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link29 rootCodes root_binding alphabets halph nonincident_complete
    FastDual29_014.pointList FastDual29_014.columns FastDual29_014.rows FastDual29_014.bound (by decide +kernel)
    FastDual29_014.column_mask FastDual29_014.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link29 alphabets) : ActualObstruction link29 {6,7,10,11} := rep014 halph

def dualQuads : List (Finset Point) := [{2,3,6,7},{2,3,6,9},{2,3,7,9},{2,3,6,10},{2,3,7,11},{2,3,6,11},{2,3,7,10},{2,3,10,11},{2,6,7,9},{3,6,7,9},{2,6,7,10},{3,6,7,11},{2,6,7,11},{3,6,7,10},{2,6,9,10},{3,7,9,11},{2,6,9,11},{3,7,9,10},{2,6,10,11},{3,7,10,11},{2,7,9,10},{3,6,9,11},{2,7,9,11},{3,6,9,10},{2,7,10,11},{3,6,10,11},{6,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link29 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link29 Q := by
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

theorem all_foursets (halph : AlphabetComplete link29 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link29 Q :=
  class_census link29 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source29
