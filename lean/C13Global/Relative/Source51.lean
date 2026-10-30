import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source51
import C13Global.FastGroups.Source51Part00
import C13Global.FastGroups.Source51Part01
namespace C13.Global.Relative.Source51
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source51
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link51 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link51 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link51 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link51 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link51 alphabets) :
    ActualObstruction link51 FastDual51_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link51 rootCodes root_binding alphabets halph nonincident_complete
    FastDual51_000.pointList FastDual51_000.columns FastDual51_000.rows FastDual51_000.bound (by decide +kernel)
    FastDual51_000.column_mask FastDual51_000.checked hc F hF hroot hmin hout

theorem query167 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {1,2,3,6} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![10,9,8,11,4,7,6,5,2,1,0,3,12]
  invFun := ![10,9,8,11,4,7,6,5,2,1,0,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link51 = link51 :=
  root_symmetry_of_codes rootCodes link51 root_binding automorphism000 (by decide +kernel)

theorem query487 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {6,8,9,11} :=
  obstruction_transport link51 FastDual51_000.points {6,8,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link51 alphabets) :
    ActualObstruction link51 FastDual51_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link51 rootCodes root_binding alphabets halph nonincident_complete
    FastDual51_001.pointList FastDual51_001.columns FastDual51_001.rows FastDual51_001.bound (by decide +kernel)
    FastDual51_001.column_mask FastDual51_001.checked hc F hF hroot hmin hout

theorem query187 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {1,2,6,8} := rep001 halph

theorem query353 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {2,6,8,9} :=
  obstruction_transport link51 FastDual51_001.points {2,6,8,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link51 alphabets) :
    ActualObstruction link51 FastDual51_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link51 rootCodes root_binding alphabets halph nonincident_complete
    FastDual51_002.pointList FastDual51_002.columns FastDual51_002.rows FastDual51_002.bound (by decide +kernel)
    FastDual51_002.column_mask FastDual51_002.checked hc F hF hroot hmin hout

theorem query188 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {1,2,6,9} := rep002 halph

theorem query269 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {1,6,8,9} :=
  obstruction_transport link51 FastDual51_002.points {1,6,8,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link51 alphabets) :
    ActualObstruction link51 FastDual51_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link51 rootCodes root_binding alphabets halph nonincident_complete
    FastDual51_003.pointList FastDual51_003.columns FastDual51_003.rows FastDual51_003.bound (by decide +kernel)
    FastDual51_003.column_mask FastDual51_003.checked hc F hF hroot hmin hout

theorem query190 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {1,2,6,11} := rep003 halph

theorem query409 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {3,6,8,9} :=
  obstruction_transport link51 FastDual51_003.points {3,6,8,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link51 alphabets) :
    ActualObstruction link51 FastDual51_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link51 rootCodes root_binding alphabets halph nonincident_complete
    FastDual51_004.pointList FastDual51_004.columns FastDual51_004.rows FastDual51_004.bound (by decide +kernel)
    FastDual51_004.column_mask FastDual51_004.checked hc F hF hroot hmin hout

theorem query197 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {1,2,8,11} := rep004 halph

theorem query307 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {2,3,8,9} :=
  obstruction_transport link51 FastDual51_004.points {2,3,8,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link51 alphabets) :
    ActualObstruction link51 FastDual51_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link51 rootCodes root_binding alphabets halph nonincident_complete
    FastDual51_005.pointList FastDual51_005.columns FastDual51_005.rows FastDual51_005.bound (by decide +kernel)
    FastDual51_005.column_mask FastDual51_005.checked hc F hF hroot hmin hout

theorem query215 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {1,3,6,8} := rep005 halph

theorem query357 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {2,6,9,11} :=
  obstruction_transport link51 FastDual51_005.points {2,6,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link51 alphabets) :
    ActualObstruction link51 FastDual51_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link51 rootCodes root_binding alphabets halph nonincident_complete
    FastDual51_006.pointList FastDual51_006.columns FastDual51_006.rows FastDual51_006.bound (by decide +kernel)
    FastDual51_006.column_mask FastDual51_006.checked hc F hF hroot hmin hout

theorem query216 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {1,3,6,9} := rep006 halph

theorem query273 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {1,6,9,11} :=
  obstruction_transport link51 FastDual51_006.points {1,6,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link51 alphabets) :
    ActualObstruction link51 FastDual51_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link51 rootCodes root_binding alphabets halph nonincident_complete
    FastDual51_007.pointList FastDual51_007.columns FastDual51_007.rows FastDual51_007.bound (by decide +kernel)
    FastDual51_007.column_mask FastDual51_007.checked hc F hF hroot hmin hout

theorem query218 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {1,3,6,11} := rep007 halph

theorem query413 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {3,6,9,11} :=
  obstruction_transport link51 FastDual51_007.points {3,6,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link51 alphabets) :
    ActualObstruction link51 FastDual51_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link51 rootCodes root_binding alphabets halph nonincident_complete
    FastDual51_008.pointList FastDual51_008.columns FastDual51_008.rows FastDual51_008.bound (by decide +kernel)
    FastDual51_008.column_mask FastDual51_008.checked hc F hF hroot hmin hout

theorem query227 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {1,3,9,11} := rep008 halph

theorem rep009 (halph : AlphabetComplete link51 alphabets) :
    ActualObstruction link51 FastDual51_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link51 rootCodes root_binding alphabets halph nonincident_complete
    FastDual51_009.pointList FastDual51_009.columns FastDual51_009.rows FastDual51_009.bound (by decide +kernel)
    FastDual51_009.column_mask FastDual51_009.checked hc F hF hroot hmin hout

theorem query271 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {1,6,8,11} := rep009 halph

theorem query300 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {2,3,6,9} :=
  obstruction_transport link51 FastDual51_009.points {2,3,6,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link51 alphabets) :
    ActualObstruction link51 FastDual51_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link51 rootCodes root_binding alphabets halph nonincident_complete
    FastDual51_010.pointList FastDual51_010.columns FastDual51_010.rows FastDual51_010.bound (by decide +kernel)
    FastDual51_010.column_mask FastDual51_010.checked hc F hF hroot hmin hout

theorem query299 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {2,3,6,8} := rep010 halph

theorem query355 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {2,6,8,11} :=
  obstruction_transport link51 FastDual51_010.points {2,6,8,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link51 alphabets) :
    ActualObstruction link51 FastDual51_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link51 rootCodes root_binding alphabets halph nonincident_complete
    FastDual51_011.pointList FastDual51_011.columns FastDual51_011.rows FastDual51_011.bound (by decide +kernel)
    FastDual51_011.column_mask FastDual51_011.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {2,3,6,11} := rep011 halph

theorem query411 (halph : AlphabetComplete link51 alphabets) : ActualObstruction link51 {3,6,8,11} :=
  obstruction_transport link51 FastDual51_011.points {3,6,8,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep011 halph)

def dualQuads : List (Finset Point) := [{1,2,3,6},{6,8,9,11},{1,2,6,8},{2,6,8,9},{1,2,6,9},{1,6,8,9},{1,2,6,11},{3,6,8,9},{1,2,8,11},{2,3,8,9},{1,3,6,8},{2,6,9,11},{1,3,6,9},{1,6,9,11},{1,3,6,11},{3,6,9,11},{1,3,9,11},{1,6,8,11},{2,3,6,9},{2,3,6,8},{2,6,8,11},{2,3,6,11},{3,6,8,11}]

theorem dual_actual (halph : AlphabetComplete link51 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link51 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query167 halph
  · exact query487 halph
  · exact query187 halph
  · exact query353 halph
  · exact query188 halph
  · exact query269 halph
  · exact query190 halph
  · exact query409 halph
  · exact query197 halph
  · exact query307 halph
  · exact query215 halph
  · exact query357 halph
  · exact query216 halph
  · exact query273 halph
  · exact query218 halph
  · exact query413 halph
  · exact query227 halph
  · exact query271 halph
  · exact query300 halph
  · exact query299 halph
  · exact query355 halph
  · exact query302 halph
  · exact query411 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link51 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link51 Q :=
  class_census link51 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source51
