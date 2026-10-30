import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source55
import C13Global.FastGroups.Source55Part00
import C13Global.FastGroups.Source55Part01
namespace C13.Global.Relative.Source55
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source55
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link55 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link55 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link55 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link55 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link55 alphabets) :
    ActualObstruction link55 FastDual55_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link55 rootCodes root_binding alphabets halph nonincident_complete
    FastDual55_000.pointList FastDual55_000.columns FastDual55_000.rows FastDual55_000.bound (by decide +kernel)
    FastDual55_000.column_mask FastDual55_000.checked hc F hF hroot hmin hout

theorem query295 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {2,3,5,9} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link55 = link55 :=
  root_symmetry_of_codes rootCodes link55 root_binding automorphism000 (by decide +kernel)

theorem query341 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {2,5,7,10} :=
  obstruction_transport link55 FastDual55_000.points {2,5,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link55 alphabets) :
    ActualObstruction link55 FastDual55_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link55 rootCodes root_binding alphabets halph nonincident_complete
    FastDual55_001.pointList FastDual55_001.columns FastDual55_001.rows FastDual55_001.bound (by decide +kernel)
    FastDual55_001.column_mask FastDual55_001.checked hc F hF hroot hmin hout

theorem query296 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {2,3,5,10} := rep001 halph

theorem query340 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {2,5,7,9} :=
  obstruction_transport link55 FastDual55_001.points {2,5,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link55 alphabets) :
    ActualObstruction link55 FastDual55_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link55 rootCodes root_binding alphabets halph nonincident_complete
    FastDual55_002.pointList FastDual55_002.columns FastDual55_002.rows FastDual55_002.bound (by decide +kernel)
    FastDual55_002.column_mask FastDual55_002.checked hc F hF hroot hmin hout

theorem query297 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {2,3,5,11} := rep002 halph

theorem query342 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {2,5,7,11} :=
  obstruction_transport link55 FastDual55_002.points {2,5,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link55 alphabets) :
    ActualObstruction link55 FastDual55_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link55 rootCodes root_binding alphabets halph nonincident_complete
    FastDual55_003.pointList FastDual55_003.columns FastDual55_003.rows FastDual55_003.bound (by decide +kernel)
    FastDual55_003.column_mask FastDual55_003.checked hc F hF hroot hmin hout

theorem query304 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {2,3,7,9} := rep003 halph

theorem query397 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {3,5,7,10} :=
  obstruction_transport link55 FastDual55_003.points {3,5,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link55 alphabets) :
    ActualObstruction link55 FastDual55_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link55 rootCodes root_binding alphabets halph nonincident_complete
    FastDual55_004.pointList FastDual55_004.columns FastDual55_004.rows FastDual55_004.bound (by decide +kernel)
    FastDual55_004.column_mask FastDual55_004.checked hc F hF hroot hmin hout

theorem query305 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {2,3,7,10} := rep004 halph

theorem query396 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {3,5,7,9} :=
  obstruction_transport link55 FastDual55_004.points {3,5,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link55 alphabets) :
    ActualObstruction link55 FastDual55_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link55 rootCodes root_binding alphabets halph nonincident_complete
    FastDual55_005.pointList FastDual55_005.columns FastDual55_005.rows FastDual55_005.bound (by decide +kernel)
    FastDual55_005.column_mask FastDual55_005.checked hc F hF hroot hmin hout

theorem query306 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {2,3,7,11} := rep005 halph

theorem query398 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {3,5,7,11} :=
  obstruction_transport link55 FastDual55_005.points {3,5,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link55 alphabets) :
    ActualObstruction link55 FastDual55_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link55 rootCodes root_binding alphabets halph nonincident_complete
    FastDual55_006.pointList FastDual55_006.columns FastDual55_006.rows FastDual55_006.bound (by decide +kernel)
    FastDual55_006.column_mask FastDual55_006.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {2,3,10,11} := rep006 halph

theorem query474 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {5,7,9,11} :=
  obstruction_transport link55 FastDual55_006.points {5,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link55 alphabets) :
    ActualObstruction link55 FastDual55_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link55 rootCodes root_binding alphabets halph nonincident_complete
    FastDual55_007.pointList FastDual55_007.columns FastDual55_007.rows FastDual55_007.bound (by decide +kernel)
    FastDual55_007.column_mask FastDual55_007.checked hc F hF hroot hmin hout

theorem query346 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {2,5,9,10} := rep007 halph

theorem rep008 (halph : AlphabetComplete link55 alphabets) :
    ActualObstruction link55 FastDual55_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link55 rootCodes root_binding alphabets halph nonincident_complete
    FastDual55_008.pointList FastDual55_008.columns FastDual55_008.rows FastDual55_008.bound (by decide +kernel)
    FastDual55_008.column_mask FastDual55_008.checked hc F hF hroot hmin hout

theorem query347 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {2,5,9,11} := rep008 halph

theorem query348 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {2,5,10,11} :=
  obstruction_transport link55 FastDual55_008.points {2,5,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link55 alphabets) :
    ActualObstruction link55 FastDual55_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link55 rootCodes root_binding alphabets halph nonincident_complete
    FastDual55_009.pointList FastDual55_009.columns FastDual55_009.rows FastDual55_009.bound (by decide +kernel)
    FastDual55_009.column_mask FastDual55_009.checked hc F hF hroot hmin hout

theorem query362 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {2,7,9,10} := rep009 halph

theorem query402 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {3,5,9,10} :=
  obstruction_transport link55 FastDual55_009.points {3,5,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link55 alphabets) :
    ActualObstruction link55 FastDual55_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link55 rootCodes root_binding alphabets halph nonincident_complete
    FastDual55_010.pointList FastDual55_010.columns FastDual55_010.rows FastDual55_010.bound (by decide +kernel)
    FastDual55_010.column_mask FastDual55_010.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {2,7,9,11} := rep010 halph

theorem query404 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {3,5,10,11} :=
  obstruction_transport link55 FastDual55_010.points {3,5,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link55 alphabets) :
    ActualObstruction link55 FastDual55_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link55 rootCodes root_binding alphabets halph nonincident_complete
    FastDual55_011.pointList FastDual55_011.columns FastDual55_011.rows FastDual55_011.bound (by decide +kernel)
    FastDual55_011.column_mask FastDual55_011.checked hc F hF hroot hmin hout

theorem query364 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {2,7,10,11} := rep011 halph

theorem query403 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {3,5,9,11} :=
  obstruction_transport link55 FastDual55_011.points {3,5,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link55 alphabets) :
    ActualObstruction link55 FastDual55_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link55 rootCodes root_binding alphabets halph nonincident_complete
    FastDual55_012.pointList FastDual55_012.columns FastDual55_012.rows FastDual55_012.bound (by decide +kernel)
    FastDual55_012.column_mask FastDual55_012.checked hc F hF hroot hmin hout

theorem query418 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {3,7,9,10} := rep012 halph

theorem rep013 (halph : AlphabetComplete link55 alphabets) :
    ActualObstruction link55 FastDual55_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link55 rootCodes root_binding alphabets halph nonincident_complete
    FastDual55_013.pointList FastDual55_013.columns FastDual55_013.rows FastDual55_013.bound (by decide +kernel)
    FastDual55_013.column_mask FastDual55_013.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {3,7,9,11} := rep013 halph

theorem query420 (halph : AlphabetComplete link55 alphabets) : ActualObstruction link55 {3,7,10,11} :=
  obstruction_transport link55 FastDual55_013.points {3,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep013 halph)

def dualQuads : List (Finset Point) := [{2,3,5,9},{2,5,7,10},{2,3,5,10},{2,5,7,9},{2,3,5,11},{2,5,7,11},{2,3,7,9},{3,5,7,10},{2,3,7,10},{3,5,7,9},{2,3,7,11},{3,5,7,11},{2,3,10,11},{5,7,9,11},{2,5,9,10},{2,5,9,11},{2,5,10,11},{2,7,9,10},{3,5,9,10},{2,7,9,11},{3,5,10,11},{2,7,10,11},{3,5,9,11},{3,7,9,10},{3,7,9,11},{3,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link55 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link55 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query295 halph
  · exact query341 halph
  · exact query296 halph
  · exact query340 halph
  · exact query297 halph
  · exact query342 halph
  · exact query304 halph
  · exact query397 halph
  · exact query305 halph
  · exact query396 halph
  · exact query306 halph
  · exact query398 halph
  · exact query312 halph
  · exact query474 halph
  · exact query346 halph
  · exact query347 halph
  · exact query348 halph
  · exact query362 halph
  · exact query402 halph
  · exact query363 halph
  · exact query404 halph
  · exact query364 halph
  · exact query403 halph
  · exact query418 halph
  · exact query419 halph
  · exact query420 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link55 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link55 Q :=
  class_census link55 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source55
