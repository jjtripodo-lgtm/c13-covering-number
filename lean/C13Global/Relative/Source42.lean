import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source42
import C13Global.FastGroups.Source42Part00
import C13Global.FastGroups.Source42Part01
namespace C13.Global.Relative.Source42
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source42
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link42 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link42 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link42 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link42 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link42 alphabets) :
    ActualObstruction link42 FastDual42_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link42 rootCodes root_binding alphabets halph nonincident_complete
    FastDual42_000.pointList FastDual42_000.columns FastDual42_000.rows FastDual42_000.bound (by decide +kernel)
    FastDual42_000.column_mask FastDual42_000.checked hc F hF hroot hmin hout

theorem query167 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {1,2,3,6} := rep000 halph

theorem rep001 (halph : AlphabetComplete link42 alphabets) :
    ActualObstruction link42 FastDual42_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link42 rootCodes root_binding alphabets halph nonincident_complete
    FastDual42_001.pointList FastDual42_001.columns FastDual42_001.rows FastDual42_001.bound (by decide +kernel)
    FastDual42_001.column_mask FastDual42_001.checked hc F hF hroot hmin hout

theorem query172 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {1,2,3,11} := rep001 halph

theorem rep002 (halph : AlphabetComplete link42 alphabets) :
    ActualObstruction link42 FastDual42_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link42 rootCodes root_binding alphabets halph nonincident_complete
    FastDual42_002.pointList FastDual42_002.columns FastDual42_002.rows FastDual42_002.bound (by decide +kernel)
    FastDual42_002.column_mask FastDual42_002.checked hc F hF hroot hmin hout

theorem query187 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {1,2,6,8} := rep002 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link42 = link42 :=
  root_symmetry_of_codes rootCodes link42 root_binding automorphism000 (by decide +kernel)

theorem query216 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {1,3,6,9} :=
  obstruction_transport link42 FastDual42_002.points {1,3,6,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link42 alphabets) :
    ActualObstruction link42 FastDual42_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link42 rootCodes root_binding alphabets halph nonincident_complete
    FastDual42_003.pointList FastDual42_003.columns FastDual42_003.rows FastDual42_003.bound (by decide +kernel)
    FastDual42_003.column_mask FastDual42_003.checked hc F hF hroot hmin hout

theorem query188 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {1,2,6,9} := rep003 halph

theorem query215 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {1,3,6,8} :=
  obstruction_transport link42 FastDual42_003.points {1,3,6,8} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link42 alphabets) :
    ActualObstruction link42 FastDual42_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link42 rootCodes root_binding alphabets halph nonincident_complete
    FastDual42_004.pointList FastDual42_004.columns FastDual42_004.rows FastDual42_004.bound (by decide +kernel)
    FastDual42_004.column_mask FastDual42_004.checked hc F hF hroot hmin hout

theorem query190 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {1,2,6,11} := rep004 halph

theorem query218 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {1,3,6,11} :=
  obstruction_transport link42 FastDual42_004.points {1,3,6,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link42 alphabets) :
    ActualObstruction link42 FastDual42_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link42 rootCodes root_binding alphabets halph nonincident_complete
    FastDual42_005.pointList FastDual42_005.columns FastDual42_005.rows FastDual42_005.bound (by decide +kernel)
    FastDual42_005.column_mask FastDual42_005.checked hc F hF hroot hmin hout

theorem query197 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {1,2,8,11} := rep005 halph

theorem query227 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {1,3,9,11} :=
  obstruction_transport link42 FastDual42_005.points {1,3,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link42 alphabets) :
    ActualObstruction link42 FastDual42_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link42 rootCodes root_binding alphabets halph nonincident_complete
    FastDual42_006.pointList FastDual42_006.columns FastDual42_006.rows FastDual42_006.bound (by decide +kernel)
    FastDual42_006.column_mask FastDual42_006.checked hc F hF hroot hmin hout

theorem query269 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {1,6,8,9} := rep006 halph

theorem rep007 (halph : AlphabetComplete link42 alphabets) :
    ActualObstruction link42 FastDual42_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link42 rootCodes root_binding alphabets halph nonincident_complete
    FastDual42_007.pointList FastDual42_007.columns FastDual42_007.rows FastDual42_007.bound (by decide +kernel)
    FastDual42_007.column_mask FastDual42_007.checked hc F hF hroot hmin hout

theorem query271 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {1,6,8,11} := rep007 halph

theorem query273 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {1,6,9,11} :=
  obstruction_transport link42 FastDual42_007.points {1,6,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link42 alphabets) :
    ActualObstruction link42 FastDual42_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link42 rootCodes root_binding alphabets halph nonincident_complete
    FastDual42_008.pointList FastDual42_008.columns FastDual42_008.rows FastDual42_008.bound (by decide +kernel)
    FastDual42_008.column_mask FastDual42_008.checked hc F hF hroot hmin hout

theorem query299 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {2,3,6,8} := rep008 halph

theorem query300 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {2,3,6,9} :=
  obstruction_transport link42 FastDual42_008.points {2,3,6,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link42 alphabets) :
    ActualObstruction link42 FastDual42_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link42 rootCodes root_binding alphabets halph nonincident_complete
    FastDual42_009.pointList FastDual42_009.columns FastDual42_009.rows FastDual42_009.bound (by decide +kernel)
    FastDual42_009.column_mask FastDual42_009.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {2,3,6,11} := rep009 halph

theorem rep010 (halph : AlphabetComplete link42 alphabets) :
    ActualObstruction link42 FastDual42_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link42 rootCodes root_binding alphabets halph nonincident_complete
    FastDual42_010.pointList FastDual42_010.columns FastDual42_010.rows FastDual42_010.bound (by decide +kernel)
    FastDual42_010.column_mask FastDual42_010.checked hc F hF hroot hmin hout

theorem query307 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {2,3,8,9} := rep010 halph

theorem rep011 (halph : AlphabetComplete link42 alphabets) :
    ActualObstruction link42 FastDual42_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link42 rootCodes root_binding alphabets halph nonincident_complete
    FastDual42_011.pointList FastDual42_011.columns FastDual42_011.rows FastDual42_011.bound (by decide +kernel)
    FastDual42_011.column_mask FastDual42_011.checked hc F hF hroot hmin hout

theorem query353 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {2,6,8,9} := rep011 halph

theorem query409 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {3,6,8,9} :=
  obstruction_transport link42 FastDual42_011.points {3,6,8,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link42 alphabets) :
    ActualObstruction link42 FastDual42_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link42 rootCodes root_binding alphabets halph nonincident_complete
    FastDual42_012.pointList FastDual42_012.columns FastDual42_012.rows FastDual42_012.bound (by decide +kernel)
    FastDual42_012.column_mask FastDual42_012.checked hc F hF hroot hmin hout

theorem query355 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {2,6,8,11} := rep012 halph

theorem query413 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {3,6,9,11} :=
  obstruction_transport link42 FastDual42_012.points {3,6,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep012 halph)

theorem rep013 (halph : AlphabetComplete link42 alphabets) :
    ActualObstruction link42 FastDual42_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link42 rootCodes root_binding alphabets halph nonincident_complete
    FastDual42_013.pointList FastDual42_013.columns FastDual42_013.rows FastDual42_013.bound (by decide +kernel)
    FastDual42_013.column_mask FastDual42_013.checked hc F hF hroot hmin hout

theorem query357 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {2,6,9,11} := rep013 halph

theorem query411 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {3,6,8,11} :=
  obstruction_transport link42 FastDual42_013.points {3,6,8,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep013 halph)

theorem rep014 (halph : AlphabetComplete link42 alphabets) :
    ActualObstruction link42 FastDual42_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link42 rootCodes root_binding alphabets halph nonincident_complete
    FastDual42_014.pointList FastDual42_014.columns FastDual42_014.rows FastDual42_014.bound (by decide +kernel)
    FastDual42_014.column_mask FastDual42_014.checked hc F hF hroot hmin hout

theorem query487 (halph : AlphabetComplete link42 alphabets) : ActualObstruction link42 {6,8,9,11} := rep014 halph

def dualQuads : List (Finset Point) := [{1,2,3,6},{1,2,3,11},{1,2,6,8},{1,3,6,9},{1,2,6,9},{1,3,6,8},{1,2,6,11},{1,3,6,11},{1,2,8,11},{1,3,9,11},{1,6,8,9},{1,6,8,11},{1,6,9,11},{2,3,6,8},{2,3,6,9},{2,3,6,11},{2,3,8,9},{2,6,8,9},{3,6,8,9},{2,6,8,11},{3,6,9,11},{2,6,9,11},{3,6,8,11},{6,8,9,11}]

theorem dual_actual (halph : AlphabetComplete link42 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link42 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query167 halph
  · exact query172 halph
  · exact query187 halph
  · exact query216 halph
  · exact query188 halph
  · exact query215 halph
  · exact query190 halph
  · exact query218 halph
  · exact query197 halph
  · exact query227 halph
  · exact query269 halph
  · exact query271 halph
  · exact query273 halph
  · exact query299 halph
  · exact query300 halph
  · exact query302 halph
  · exact query307 halph
  · exact query353 halph
  · exact query409 halph
  · exact query355 halph
  · exact query413 halph
  · exact query357 halph
  · exact query411 halph
  · exact query487 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link42 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link42 Q :=
  class_census link42 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source42
