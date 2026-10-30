import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source56
import C13Global.FastGroups.Source56Part00
import C13Global.FastGroups.Source56Part01
namespace C13.Global.Relative.Source56
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source56
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link56 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link56 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link56 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link56 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link56 alphabets) :
    ActualObstruction link56 FastDual56_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link56 rootCodes root_binding alphabets halph nonincident_complete
    FastDual56_000.pointList FastDual56_000.columns FastDual56_000.rows FastDual56_000.bound (by decide +kernel)
    FastDual56_000.column_mask FastDual56_000.checked hc F hF hroot hmin hout

theorem query166 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {1,2,3,5} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![0,2,1,3,8,10,9,11,4,6,5,7,12]
  invFun := ![0,2,1,3,8,10,9,11,4,6,5,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link56 = link56 :=
  root_symmetry_of_codes rootCodes link56 root_binding automorphism000 (by decide +kernel)

theorem query171 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {1,2,3,10} :=
  obstruction_transport link56 FastDual56_000.points {1,2,3,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link56 alphabets) :
    ActualObstruction link56 FastDual56_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link56 rootCodes root_binding alphabets halph nonincident_complete
    FastDual56_001.pointList FastDual56_001.columns FastDual56_001.rows FastDual56_001.bound (by decide +kernel)
    FastDual56_001.column_mask FastDual56_001.checked hc F hF hroot hmin hout

theorem query184 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {1,2,5,10} := rep001 halph

theorem rep002 (halph : AlphabetComplete link56 alphabets) :
    ActualObstruction link56 FastDual56_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link56 rootCodes root_binding alphabets halph nonincident_complete
    FastDual56_002.pointList FastDual56_002.columns FastDual56_002.rows FastDual56_002.bound (by decide +kernel)
    FastDual56_002.column_mask FastDual56_002.checked hc F hF hroot hmin hout

theorem query185 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {1,2,5,11} := rep002 halph

theorem query193 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {1,2,7,10} :=
  obstruction_transport link56 FastDual56_002.points {1,2,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link56 alphabets) :
    ActualObstruction link56 FastDual56_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link56 rootCodes root_binding alphabets halph nonincident_complete
    FastDual56_003.pointList FastDual56_003.columns FastDual56_003.rows FastDual56_003.bound (by decide +kernel)
    FastDual56_003.column_mask FastDual56_003.checked hc F hF hroot hmin hout

theorem query194 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {1,2,7,11} := rep003 halph

theorem rep004 (halph : AlphabetComplete link56 alphabets) :
    ActualObstruction link56 FastDual56_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link56 rootCodes root_binding alphabets halph nonincident_complete
    FastDual56_004.pointList FastDual56_004.columns FastDual56_004.rows FastDual56_004.bound (by decide +kernel)
    FastDual56_004.column_mask FastDual56_004.checked hc F hF hroot hmin hout

theorem query209 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {1,3,5,7} := rep004 halph

theorem query312 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {2,3,10,11} :=
  obstruction_transport link56 FastDual56_004.points {2,3,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link56 alphabets) :
    ActualObstruction link56 FastDual56_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link56 rootCodes root_binding alphabets halph nonincident_complete
    FastDual56_005.pointList FastDual56_005.columns FastDual56_005.rows FastDual56_005.bound (by decide +kernel)
    FastDual56_005.column_mask FastDual56_005.checked hc F hF hroot hmin hout

theorem query212 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {1,3,5,10} := rep005 halph

theorem query296 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {2,3,5,10} :=
  obstruction_transport link56 FastDual56_005.points {2,3,5,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link56 alphabets) :
    ActualObstruction link56 FastDual56_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link56 rootCodes root_binding alphabets halph nonincident_complete
    FastDual56_006.pointList FastDual56_006.columns FastDual56_006.rows FastDual56_006.bound (by decide +kernel)
    FastDual56_006.column_mask FastDual56_006.checked hc F hF hroot hmin hout

theorem query213 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {1,3,5,11} := rep006 halph

theorem query305 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {2,3,7,10} :=
  obstruction_transport link56 FastDual56_006.points {2,3,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link56 alphabets) :
    ActualObstruction link56 FastDual56_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link56 rootCodes root_binding alphabets halph nonincident_complete
    FastDual56_007.pointList FastDual56_007.columns FastDual56_007.rows FastDual56_007.bound (by decide +kernel)
    FastDual56_007.column_mask FastDual56_007.checked hc F hF hroot hmin hout

theorem query221 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {1,3,7,10} := rep007 halph

theorem query297 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {2,3,5,11} :=
  obstruction_transport link56 FastDual56_007.points {2,3,5,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link56 alphabets) :
    ActualObstruction link56 FastDual56_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link56 rootCodes root_binding alphabets halph nonincident_complete
    FastDual56_008.pointList FastDual56_008.columns FastDual56_008.rows FastDual56_008.bound (by decide +kernel)
    FastDual56_008.column_mask FastDual56_008.checked hc F hF hroot hmin hout

theorem query222 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {1,3,7,11} := rep008 halph

theorem query306 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {2,3,7,11} :=
  obstruction_transport link56 FastDual56_008.points {2,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link56 alphabets) :
    ActualObstruction link56 FastDual56_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link56 rootCodes root_binding alphabets halph nonincident_complete
    FastDual56_009.pointList FastDual56_009.columns FastDual56_009.rows FastDual56_009.bound (by decide +kernel)
    FastDual56_009.column_mask FastDual56_009.checked hc F hF hroot hmin hout

theorem query257 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {1,5,7,10} := rep009 halph

theorem query348 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {2,5,10,11} :=
  obstruction_transport link56 FastDual56_009.points {2,5,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link56 alphabets) :
    ActualObstruction link56 FastDual56_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link56 rootCodes root_binding alphabets halph nonincident_complete
    FastDual56_010.pointList FastDual56_010.columns FastDual56_010.rows FastDual56_010.bound (by decide +kernel)
    FastDual56_010.column_mask FastDual56_010.checked hc F hF hroot hmin hout

theorem query258 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {1,5,7,11} := rep010 halph

theorem query364 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {2,7,10,11} :=
  obstruction_transport link56 FastDual56_010.points {2,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link56 alphabets) :
    ActualObstruction link56 FastDual56_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link56 rootCodes root_binding alphabets halph nonincident_complete
    FastDual56_011.pointList FastDual56_011.columns FastDual56_011.rows FastDual56_011.bound (by decide +kernel)
    FastDual56_011.column_mask FastDual56_011.checked hc F hF hroot hmin hout

theorem query264 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {1,5,10,11} := rep011 halph

theorem query341 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {2,5,7,10} :=
  obstruction_transport link56 FastDual56_011.points {2,5,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link56 alphabets) :
    ActualObstruction link56 FastDual56_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link56 rootCodes root_binding alphabets halph nonincident_complete
    FastDual56_012.pointList FastDual56_012.columns FastDual56_012.rows FastDual56_012.bound (by decide +kernel)
    FastDual56_012.column_mask FastDual56_012.checked hc F hF hroot hmin hout

theorem query280 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {1,7,10,11} := rep012 halph

theorem query342 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {2,5,7,11} :=
  obstruction_transport link56 FastDual56_012.points {2,5,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep012 halph)

theorem rep013 (halph : AlphabetComplete link56 alphabets) :
    ActualObstruction link56 FastDual56_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link56 rootCodes root_binding alphabets halph nonincident_complete
    FastDual56_013.pointList FastDual56_013.columns FastDual56_013.rows FastDual56_013.bound (by decide +kernel)
    FastDual56_013.column_mask FastDual56_013.checked hc F hF hroot hmin hout

theorem query397 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {3,5,7,10} := rep013 halph

theorem query404 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {3,5,10,11} :=
  obstruction_transport link56 FastDual56_013.points {3,5,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep013 halph)

theorem rep014 (halph : AlphabetComplete link56 alphabets) :
    ActualObstruction link56 FastDual56_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link56 rootCodes root_binding alphabets halph nonincident_complete
    FastDual56_014.pointList FastDual56_014.columns FastDual56_014.rows FastDual56_014.bound (by decide +kernel)
    FastDual56_014.column_mask FastDual56_014.checked hc F hF hroot hmin hout

theorem query398 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {3,5,7,11} := rep014 halph

theorem query420 (halph : AlphabetComplete link56 alphabets) : ActualObstruction link56 {3,7,10,11} :=
  obstruction_transport link56 FastDual56_014.points {3,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep014 halph)

def dualQuads : List (Finset Point) := [{1,2,3,5},{1,2,3,10},{1,2,5,10},{1,2,5,11},{1,2,7,10},{1,2,7,11},{1,3,5,7},{2,3,10,11},{1,3,5,10},{2,3,5,10},{1,3,5,11},{2,3,7,10},{1,3,7,10},{2,3,5,11},{1,3,7,11},{2,3,7,11},{1,5,7,10},{2,5,10,11},{1,5,7,11},{2,7,10,11},{1,5,10,11},{2,5,7,10},{1,7,10,11},{2,5,7,11},{3,5,7,10},{3,5,10,11},{3,5,7,11},{3,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link56 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link56 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query166 halph
  · exact query171 halph
  · exact query184 halph
  · exact query185 halph
  · exact query193 halph
  · exact query194 halph
  · exact query209 halph
  · exact query312 halph
  · exact query212 halph
  · exact query296 halph
  · exact query213 halph
  · exact query305 halph
  · exact query221 halph
  · exact query297 halph
  · exact query222 halph
  · exact query306 halph
  · exact query257 halph
  · exact query348 halph
  · exact query258 halph
  · exact query364 halph
  · exact query264 halph
  · exact query341 halph
  · exact query280 halph
  · exact query342 halph
  · exact query397 halph
  · exact query404 halph
  · exact query398 halph
  · exact query420 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link56 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link56 Q :=
  class_census link56 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source56
