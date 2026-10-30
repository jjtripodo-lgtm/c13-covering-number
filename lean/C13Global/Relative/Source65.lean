import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source65
import C13Global.FastGroups.Source65Part00
import C13Global.FastGroups.Source65Part01
import C13Global.FastGroups.Source65Part02
namespace C13.Global.Relative.Source65
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source65
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link65 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link65 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link65 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link65 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_000.pointList FastDual65_000.columns FastDual65_000.rows FastDual65_000.bound (by decide +kernel)
    FastDual65_000.column_mask FastDual65_000.checked hc F hF hroot hmin hout

theorem query088 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,3,5,6} := rep000 halph

theorem rep001 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_001.pointList FastDual65_001.columns FastDual65_001.rows FastDual65_001.bound (by decide +kernel)
    FastDual65_001.column_mask FastDual65_001.checked hc F hF hroot hmin hout

theorem query091 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,3,5,9} := rep001 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![5,4,7,6,1,0,3,2,8,9,10,11,12]
  invFun := ![5,4,7,6,1,0,3,2,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link65 = link65 :=
  root_symmetry_of_codes rootCodes link65 root_binding automorphism000 (by decide +kernel)

theorem query132 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,5,6,9} :=
  obstruction_transport link65 FastDual65_001.points {0,5,6,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_002.pointList FastDual65_002.columns FastDual65_002.rows FastDual65_002.bound (by decide +kernel)
    FastDual65_002.column_mask FastDual65_002.checked hc F hF hroot hmin hout

theorem query092 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,3,5,10} := rep002 halph

theorem query133 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,5,6,10} :=
  obstruction_transport link65 FastDual65_002.points {0,5,6,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_003.pointList FastDual65_003.columns FastDual65_003.rows FastDual65_003.bound (by decide +kernel)
    FastDual65_003.column_mask FastDual65_003.checked hc F hF hroot hmin hout

theorem query093 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,3,5,11} := rep003 halph

theorem query134 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,5,6,11} :=
  obstruction_transport link65 FastDual65_003.points {0,5,6,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_004.pointList FastDual65_004.columns FastDual65_004.rows FastDual65_004.bound (by decide +kernel)
    FastDual65_004.column_mask FastDual65_004.checked hc F hF hroot hmin hout

theorem query096 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,3,6,9} := rep004 halph

theorem query392 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {3,5,6,9} :=
  obstruction_transport link65 FastDual65_004.points {3,5,6,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_005.pointList FastDual65_005.columns FastDual65_005.rows FastDual65_005.bound (by decide +kernel)
    FastDual65_005.column_mask FastDual65_005.checked hc F hF hroot hmin hout

theorem query097 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,3,6,10} := rep005 halph

theorem query393 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {3,5,6,10} :=
  obstruction_transport link65 FastDual65_005.points {3,5,6,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_006.pointList FastDual65_006.columns FastDual65_006.rows FastDual65_006.bound (by decide +kernel)
    FastDual65_006.column_mask FastDual65_006.checked hc F hF hroot hmin hout

theorem query098 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,3,6,11} := rep006 halph

theorem query394 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {3,5,6,11} :=
  obstruction_transport link65 FastDual65_006.points {3,5,6,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_007.pointList FastDual65_007.columns FastDual65_007.rows FastDual65_007.bound (by decide +kernel)
    FastDual65_007.column_mask FastDual65_007.checked hc F hF hroot hmin hout

theorem query106 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,3,9,10} := rep007 halph

theorem query467 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {5,6,9,10} :=
  obstruction_transport link65 FastDual65_007.points {5,6,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_008.pointList FastDual65_008.columns FastDual65_008.rows FastDual65_008.bound (by decide +kernel)
    FastDual65_008.column_mask FastDual65_008.checked hc F hF hroot hmin hout

theorem query142 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,5,9,10} := rep008 halph

theorem rep009 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_009.pointList FastDual65_009.columns FastDual65_009.rows FastDual65_009.bound (by decide +kernel)
    FastDual65_009.column_mask FastDual65_009.checked hc F hF hroot hmin hout

theorem query143 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,5,9,11} := rep009 halph

theorem rep010 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_010.pointList FastDual65_010.columns FastDual65_010.rows FastDual65_010.bound (by decide +kernel)
    FastDual65_010.column_mask FastDual65_010.checked hc F hF hroot hmin hout

theorem query144 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,5,10,11} := rep010 halph

theorem rep011 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_011.pointList FastDual65_011.columns FastDual65_011.rows FastDual65_011.bound (by decide +kernel)
    FastDual65_011.column_mask FastDual65_011.checked hc F hF hroot hmin hout

theorem query152 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,6,9,10} := rep011 halph

theorem query402 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {3,5,9,10} :=
  obstruction_transport link65 FastDual65_011.points {3,5,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_012.pointList FastDual65_012.columns FastDual65_012.rows FastDual65_012.bound (by decide +kernel)
    FastDual65_012.column_mask FastDual65_012.checked hc F hF hroot hmin hout

theorem query153 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,6,9,11} := rep012 halph

theorem query403 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {3,5,9,11} :=
  obstruction_transport link65 FastDual65_012.points {3,5,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep012 halph)

theorem rep013 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_013.pointList FastDual65_013.columns FastDual65_013.rows FastDual65_013.bound (by decide +kernel)
    FastDual65_013.column_mask FastDual65_013.checked hc F hF hroot hmin hout

theorem query154 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,6,10,11} := rep013 halph

theorem query404 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {3,5,10,11} :=
  obstruction_transport link65 FastDual65_013.points {3,5,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep013 halph)

theorem rep014 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_014.pointList FastDual65_014.columns FastDual65_014.rows FastDual65_014.bound (by decide +kernel)
    FastDual65_014.column_mask FastDual65_014.checked hc F hF hroot hmin hout

theorem query164 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {0,9,10,11} := rep014 halph

theorem query479 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {5,9,10,11} :=
  obstruction_transport link65 FastDual65_014.points {5,9,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep014 halph)

theorem rep015 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_015.pointList FastDual65_015.columns FastDual65_015.rows FastDual65_015.bound (by decide +kernel)
    FastDual65_015.column_mask FastDual65_015.checked hc F hF hroot hmin hout

theorem query412 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {3,6,9,10} := rep015 halph

theorem rep016 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_016.pointList FastDual65_016.columns FastDual65_016.rows FastDual65_016.bound (by decide +kernel)
    FastDual65_016.column_mask FastDual65_016.checked hc F hF hroot hmin hout

theorem query413 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {3,6,9,11} := rep016 halph

theorem rep017 (halph : AlphabetComplete link65 alphabets) :
    ActualObstruction link65 FastDual65_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link65 rootCodes root_binding alphabets halph nonincident_complete
    FastDual65_017.pointList FastDual65_017.columns FastDual65_017.rows FastDual65_017.bound (by decide +kernel)
    FastDual65_017.column_mask FastDual65_017.checked hc F hF hroot hmin hout

theorem query414 (halph : AlphabetComplete link65 alphabets) : ActualObstruction link65 {3,6,10,11} := rep017 halph

def dualQuads : List (Finset Point) := [{0,3,5,6},{0,3,5,9},{0,5,6,9},{0,3,5,10},{0,5,6,10},{0,3,5,11},{0,5,6,11},{0,3,6,9},{3,5,6,9},{0,3,6,10},{3,5,6,10},{0,3,6,11},{3,5,6,11},{0,3,9,10},{5,6,9,10},{0,5,9,10},{0,5,9,11},{0,5,10,11},{0,6,9,10},{3,5,9,10},{0,6,9,11},{3,5,9,11},{0,6,10,11},{3,5,10,11},{0,9,10,11},{5,9,10,11},{3,6,9,10},{3,6,9,11},{3,6,10,11}]

theorem dual_actual (halph : AlphabetComplete link65 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link65 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query088 halph
  · exact query091 halph
  · exact query132 halph
  · exact query092 halph
  · exact query133 halph
  · exact query093 halph
  · exact query134 halph
  · exact query096 halph
  · exact query392 halph
  · exact query097 halph
  · exact query393 halph
  · exact query098 halph
  · exact query394 halph
  · exact query106 halph
  · exact query467 halph
  · exact query142 halph
  · exact query143 halph
  · exact query144 halph
  · exact query152 halph
  · exact query402 halph
  · exact query153 halph
  · exact query403 halph
  · exact query154 halph
  · exact query404 halph
  · exact query164 halph
  · exact query479 halph
  · exact query412 halph
  · exact query413 halph
  · exact query414 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link65 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link65 Q :=
  class_census link65 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source65
