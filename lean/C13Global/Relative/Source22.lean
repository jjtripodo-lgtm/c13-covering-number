import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source22
import C13Global.FastGroups.Source22Part00
import C13Global.FastGroups.Source22Part01
import C13Global.FastGroups.Source22Part02
import C13Global.FastGroups.Source22Part03
namespace C13.Global.Relative.Source22
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source22
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link22 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link22 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link22 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link22 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_000.pointList FastDual22_000.columns FastDual22_000.rows FastDual22_000.bound (by decide +kernel)
    FastDual22_000.column_mask FastDual22_000.checked hc F hF hroot hmin hout

theorem query215 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {1,3,6,8} := rep000 halph

theorem rep001 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_001.pointList FastDual22_001.columns FastDual22_001.rows FastDual22_001.bound (by decide +kernel)
    FastDual22_001.column_mask FastDual22_001.checked hc F hF hroot hmin hout

theorem query216 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {1,3,6,9} := rep001 halph

theorem rep002 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_002.pointList FastDual22_002.columns FastDual22_002.rows FastDual22_002.bound (by decide +kernel)
    FastDual22_002.column_mask FastDual22_002.checked hc F hF hroot hmin hout

theorem query218 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {1,3,6,11} := rep002 halph

theorem rep003 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_003.pointList FastDual22_003.columns FastDual22_003.rows FastDual22_003.bound (by decide +kernel)
    FastDual22_003.column_mask FastDual22_003.checked hc F hF hroot hmin hout

theorem query219 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {1,3,7,8} := rep003 halph

theorem rep004 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_004.pointList FastDual22_004.columns FastDual22_004.rows FastDual22_004.bound (by decide +kernel)
    FastDual22_004.column_mask FastDual22_004.checked hc F hF hroot hmin hout

theorem query220 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {1,3,7,9} := rep004 halph

theorem rep005 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_005.pointList FastDual22_005.columns FastDual22_005.rows FastDual22_005.bound (by decide +kernel)
    FastDual22_005.column_mask FastDual22_005.checked hc F hF hroot hmin hout

theorem query222 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {1,3,7,11} := rep005 halph

theorem rep006 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_006.pointList FastDual22_006.columns FastDual22_006.rows FastDual22_006.bound (by decide +kernel)
    FastDual22_006.column_mask FastDual22_006.checked hc F hF hroot hmin hout

theorem query227 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {1,3,9,11} := rep006 halph

theorem rep007 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_007.pointList FastDual22_007.columns FastDual22_007.rows FastDual22_007.bound (by decide +kernel)
    FastDual22_007.column_mask FastDual22_007.checked hc F hF hroot hmin hout

theorem query265 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {1,6,7,8} := rep007 halph

theorem rep008 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_008.pointList FastDual22_008.columns FastDual22_008.rows FastDual22_008.bound (by decide +kernel)
    FastDual22_008.column_mask FastDual22_008.checked hc F hF hroot hmin hout

theorem query266 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {1,6,7,9} := rep008 halph

theorem rep009 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_009.pointList FastDual22_009.columns FastDual22_009.rows FastDual22_009.bound (by decide +kernel)
    FastDual22_009.column_mask FastDual22_009.checked hc F hF hroot hmin hout

theorem query268 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {1,6,7,11} := rep009 halph

theorem rep010 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_010.pointList FastDual22_010.columns FastDual22_010.rows FastDual22_010.bound (by decide +kernel)
    FastDual22_010.column_mask FastDual22_010.checked hc F hF hroot hmin hout

theorem query269 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {1,6,8,9} := rep010 halph

theorem rep011 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_011.pointList FastDual22_011.columns FastDual22_011.rows FastDual22_011.bound (by decide +kernel)
    FastDual22_011.column_mask FastDual22_011.checked hc F hF hroot hmin hout

theorem query271 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {1,6,8,11} := rep011 halph

theorem rep012 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_012.pointList FastDual22_012.columns FastDual22_012.rows FastDual22_012.bound (by decide +kernel)
    FastDual22_012.column_mask FastDual22_012.checked hc F hF hroot hmin hout

theorem query273 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {1,6,9,11} := rep012 halph

theorem rep013 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_013.pointList FastDual22_013.columns FastDual22_013.rows FastDual22_013.bound (by decide +kernel)
    FastDual22_013.column_mask FastDual22_013.checked hc F hF hroot hmin hout

theorem query275 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {1,7,8,9} := rep013 halph

theorem rep014 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_014.pointList FastDual22_014.columns FastDual22_014.rows FastDual22_014.bound (by decide +kernel)
    FastDual22_014.column_mask FastDual22_014.checked hc F hF hroot hmin hout

theorem query277 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {1,7,8,11} := rep014 halph

theorem rep015 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_015.pointList FastDual22_015.columns FastDual22_015.rows FastDual22_015.bound (by decide +kernel)
    FastDual22_015.column_mask FastDual22_015.checked hc F hF hroot hmin hout

theorem query279 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {1,7,9,11} := rep015 halph

theorem rep016 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_016.pointList FastDual22_016.columns FastDual22_016.rows FastDual22_016.bound (by decide +kernel)
    FastDual22_016.column_mask FastDual22_016.checked hc F hF hroot hmin hout

theorem query405 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {3,6,7,8} := rep016 halph

theorem rep017 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_017.pointList FastDual22_017.columns FastDual22_017.rows FastDual22_017.bound (by decide +kernel)
    FastDual22_017.column_mask FastDual22_017.checked hc F hF hroot hmin hout

theorem query406 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {3,6,7,9} := rep017 halph

theorem rep018 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_018.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_018.pointList FastDual22_018.columns FastDual22_018.rows FastDual22_018.bound (by decide +kernel)
    FastDual22_018.column_mask FastDual22_018.checked hc F hF hroot hmin hout

theorem query408 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {3,6,7,11} := rep018 halph

theorem rep019 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_019.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_019.pointList FastDual22_019.columns FastDual22_019.rows FastDual22_019.bound (by decide +kernel)
    FastDual22_019.column_mask FastDual22_019.checked hc F hF hroot hmin hout

theorem query409 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {3,6,8,9} := rep019 halph

theorem rep020 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_020.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_020.pointList FastDual22_020.columns FastDual22_020.rows FastDual22_020.bound (by decide +kernel)
    FastDual22_020.column_mask FastDual22_020.checked hc F hF hroot hmin hout

theorem query411 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {3,6,8,11} := rep020 halph

theorem rep021 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_021.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_021.pointList FastDual22_021.columns FastDual22_021.rows FastDual22_021.bound (by decide +kernel)
    FastDual22_021.column_mask FastDual22_021.checked hc F hF hroot hmin hout

theorem query413 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {3,6,9,11} := rep021 halph

theorem rep022 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_022.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_022.pointList FastDual22_022.columns FastDual22_022.rows FastDual22_022.bound (by decide +kernel)
    FastDual22_022.column_mask FastDual22_022.checked hc F hF hroot hmin hout

theorem query415 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {3,7,8,9} := rep022 halph

theorem rep023 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_023.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_023.pointList FastDual22_023.columns FastDual22_023.rows FastDual22_023.bound (by decide +kernel)
    FastDual22_023.column_mask FastDual22_023.checked hc F hF hroot hmin hout

theorem query417 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {3,7,8,11} := rep023 halph

theorem rep024 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_024.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_024.pointList FastDual22_024.columns FastDual22_024.rows FastDual22_024.bound (by decide +kernel)
    FastDual22_024.column_mask FastDual22_024.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {3,7,9,11} := rep024 halph

theorem rep025 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_025.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_025.pointList FastDual22_025.columns FastDual22_025.rows FastDual22_025.bound (by decide +kernel)
    FastDual22_025.column_mask FastDual22_025.checked hc F hF hroot hmin hout

theorem query480 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {6,7,8,9} := rep025 halph

theorem rep026 (halph : AlphabetComplete link22 alphabets) :
    ActualObstruction link22 FastDual22_026.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link22 rootCodes root_binding alphabets halph nonincident_complete
    FastDual22_026.pointList FastDual22_026.columns FastDual22_026.rows FastDual22_026.bound (by decide +kernel)
    FastDual22_026.column_mask FastDual22_026.checked hc F hF hroot hmin hout

theorem query487 (halph : AlphabetComplete link22 alphabets) : ActualObstruction link22 {6,8,9,11} := rep026 halph

def dualQuads : List (Finset Point) := [{1,3,6,8},{1,3,6,9},{1,3,6,11},{1,3,7,8},{1,3,7,9},{1,3,7,11},{1,3,9,11},{1,6,7,8},{1,6,7,9},{1,6,7,11},{1,6,8,9},{1,6,8,11},{1,6,9,11},{1,7,8,9},{1,7,8,11},{1,7,9,11},{3,6,7,8},{3,6,7,9},{3,6,7,11},{3,6,8,9},{3,6,8,11},{3,6,9,11},{3,7,8,9},{3,7,8,11},{3,7,9,11},{6,7,8,9},{6,8,9,11}]

theorem dual_actual (halph : AlphabetComplete link22 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link22 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query215 halph
  · exact query216 halph
  · exact query218 halph
  · exact query219 halph
  · exact query220 halph
  · exact query222 halph
  · exact query227 halph
  · exact query265 halph
  · exact query266 halph
  · exact query268 halph
  · exact query269 halph
  · exact query271 halph
  · exact query273 halph
  · exact query275 halph
  · exact query277 halph
  · exact query279 halph
  · exact query405 halph
  · exact query406 halph
  · exact query408 halph
  · exact query409 halph
  · exact query411 halph
  · exact query413 halph
  · exact query415 halph
  · exact query417 halph
  · exact query419 halph
  · exact query480 halph
  · exact query487 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link22 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link22 Q :=
  class_census link22 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source22
