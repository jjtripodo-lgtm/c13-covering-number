import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source47
import C13Global.FastGroups.Source47Part00
import C13Global.FastGroups.Source47Part01
import C13Global.FastGroups.Source47Part02
import C13Global.FastGroups.Source47Part03
namespace C13.Global.Relative.Source47
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source47
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link47 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link47 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link47 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link47 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_000.pointList FastDual47_000.columns FastDual47_000.rows FastDual47_000.bound (by decide +kernel)
    FastDual47_000.column_mask FastDual47_000.checked hc F hF hroot hmin hout

theorem query215 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {1,3,6,8} := rep000 halph

theorem rep001 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_001.pointList FastDual47_001.columns FastDual47_001.rows FastDual47_001.bound (by decide +kernel)
    FastDual47_001.column_mask FastDual47_001.checked hc F hF hroot hmin hout

theorem query216 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {1,3,6,9} := rep001 halph

theorem rep002 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_002.pointList FastDual47_002.columns FastDual47_002.rows FastDual47_002.bound (by decide +kernel)
    FastDual47_002.column_mask FastDual47_002.checked hc F hF hroot hmin hout

theorem query218 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {1,3,6,11} := rep002 halph

theorem rep003 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_003.pointList FastDual47_003.columns FastDual47_003.rows FastDual47_003.bound (by decide +kernel)
    FastDual47_003.column_mask FastDual47_003.checked hc F hF hroot hmin hout

theorem query219 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {1,3,7,8} := rep003 halph

theorem rep004 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_004.pointList FastDual47_004.columns FastDual47_004.rows FastDual47_004.bound (by decide +kernel)
    FastDual47_004.column_mask FastDual47_004.checked hc F hF hroot hmin hout

theorem query220 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {1,3,7,9} := rep004 halph

theorem rep005 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_005.pointList FastDual47_005.columns FastDual47_005.rows FastDual47_005.bound (by decide +kernel)
    FastDual47_005.column_mask FastDual47_005.checked hc F hF hroot hmin hout

theorem query222 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {1,3,7,11} := rep005 halph

theorem rep006 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_006.pointList FastDual47_006.columns FastDual47_006.rows FastDual47_006.bound (by decide +kernel)
    FastDual47_006.column_mask FastDual47_006.checked hc F hF hroot hmin hout

theorem query227 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {1,3,9,11} := rep006 halph

theorem rep007 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_007.pointList FastDual47_007.columns FastDual47_007.rows FastDual47_007.bound (by decide +kernel)
    FastDual47_007.column_mask FastDual47_007.checked hc F hF hroot hmin hout

theorem query265 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {1,6,7,8} := rep007 halph

theorem rep008 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_008.pointList FastDual47_008.columns FastDual47_008.rows FastDual47_008.bound (by decide +kernel)
    FastDual47_008.column_mask FastDual47_008.checked hc F hF hroot hmin hout

theorem query266 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {1,6,7,9} := rep008 halph

theorem rep009 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_009.pointList FastDual47_009.columns FastDual47_009.rows FastDual47_009.bound (by decide +kernel)
    FastDual47_009.column_mask FastDual47_009.checked hc F hF hroot hmin hout

theorem query268 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {1,6,7,11} := rep009 halph

theorem rep010 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_010.pointList FastDual47_010.columns FastDual47_010.rows FastDual47_010.bound (by decide +kernel)
    FastDual47_010.column_mask FastDual47_010.checked hc F hF hroot hmin hout

theorem query269 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {1,6,8,9} := rep010 halph

theorem rep011 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_011.pointList FastDual47_011.columns FastDual47_011.rows FastDual47_011.bound (by decide +kernel)
    FastDual47_011.column_mask FastDual47_011.checked hc F hF hroot hmin hout

theorem query271 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {1,6,8,11} := rep011 halph

theorem rep012 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_012.pointList FastDual47_012.columns FastDual47_012.rows FastDual47_012.bound (by decide +kernel)
    FastDual47_012.column_mask FastDual47_012.checked hc F hF hroot hmin hout

theorem query273 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {1,6,9,11} := rep012 halph

theorem rep013 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_013.pointList FastDual47_013.columns FastDual47_013.rows FastDual47_013.bound (by decide +kernel)
    FastDual47_013.column_mask FastDual47_013.checked hc F hF hroot hmin hout

theorem query275 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {1,7,8,9} := rep013 halph

theorem rep014 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_014.pointList FastDual47_014.columns FastDual47_014.rows FastDual47_014.bound (by decide +kernel)
    FastDual47_014.column_mask FastDual47_014.checked hc F hF hroot hmin hout

theorem query277 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {1,7,8,11} := rep014 halph

theorem rep015 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_015.pointList FastDual47_015.columns FastDual47_015.rows FastDual47_015.bound (by decide +kernel)
    FastDual47_015.column_mask FastDual47_015.checked hc F hF hroot hmin hout

theorem query279 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {1,7,9,11} := rep015 halph

theorem rep016 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_016.pointList FastDual47_016.columns FastDual47_016.rows FastDual47_016.bound (by decide +kernel)
    FastDual47_016.column_mask FastDual47_016.checked hc F hF hroot hmin hout

theorem query405 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {3,6,7,8} := rep016 halph

theorem rep017 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_017.pointList FastDual47_017.columns FastDual47_017.rows FastDual47_017.bound (by decide +kernel)
    FastDual47_017.column_mask FastDual47_017.checked hc F hF hroot hmin hout

theorem query406 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {3,6,7,9} := rep017 halph

theorem rep018 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_018.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_018.pointList FastDual47_018.columns FastDual47_018.rows FastDual47_018.bound (by decide +kernel)
    FastDual47_018.column_mask FastDual47_018.checked hc F hF hroot hmin hout

theorem query408 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {3,6,7,11} := rep018 halph

theorem rep019 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_019.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_019.pointList FastDual47_019.columns FastDual47_019.rows FastDual47_019.bound (by decide +kernel)
    FastDual47_019.column_mask FastDual47_019.checked hc F hF hroot hmin hout

theorem query409 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {3,6,8,9} := rep019 halph

theorem rep020 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_020.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_020.pointList FastDual47_020.columns FastDual47_020.rows FastDual47_020.bound (by decide +kernel)
    FastDual47_020.column_mask FastDual47_020.checked hc F hF hroot hmin hout

theorem query411 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {3,6,8,11} := rep020 halph

theorem rep021 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_021.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_021.pointList FastDual47_021.columns FastDual47_021.rows FastDual47_021.bound (by decide +kernel)
    FastDual47_021.column_mask FastDual47_021.checked hc F hF hroot hmin hout

theorem query413 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {3,6,9,11} := rep021 halph

theorem rep022 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_022.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_022.pointList FastDual47_022.columns FastDual47_022.rows FastDual47_022.bound (by decide +kernel)
    FastDual47_022.column_mask FastDual47_022.checked hc F hF hroot hmin hout

theorem query415 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {3,7,8,9} := rep022 halph

theorem rep023 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_023.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_023.pointList FastDual47_023.columns FastDual47_023.rows FastDual47_023.bound (by decide +kernel)
    FastDual47_023.column_mask FastDual47_023.checked hc F hF hroot hmin hout

theorem query417 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {3,7,8,11} := rep023 halph

theorem rep024 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_024.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_024.pointList FastDual47_024.columns FastDual47_024.rows FastDual47_024.bound (by decide +kernel)
    FastDual47_024.column_mask FastDual47_024.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {3,7,9,11} := rep024 halph

theorem rep025 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_025.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_025.pointList FastDual47_025.columns FastDual47_025.rows FastDual47_025.bound (by decide +kernel)
    FastDual47_025.column_mask FastDual47_025.checked hc F hF hroot hmin hout

theorem query480 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {6,7,8,9} := rep025 halph

theorem rep026 (halph : AlphabetComplete link47 alphabets) :
    ActualObstruction link47 FastDual47_026.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link47 rootCodes root_binding alphabets halph nonincident_complete
    FastDual47_026.pointList FastDual47_026.columns FastDual47_026.rows FastDual47_026.bound (by decide +kernel)
    FastDual47_026.column_mask FastDual47_026.checked hc F hF hroot hmin hout

theorem query487 (halph : AlphabetComplete link47 alphabets) : ActualObstruction link47 {6,8,9,11} := rep026 halph

def dualQuads : List (Finset Point) := [{1,3,6,8},{1,3,6,9},{1,3,6,11},{1,3,7,8},{1,3,7,9},{1,3,7,11},{1,3,9,11},{1,6,7,8},{1,6,7,9},{1,6,7,11},{1,6,8,9},{1,6,8,11},{1,6,9,11},{1,7,8,9},{1,7,8,11},{1,7,9,11},{3,6,7,8},{3,6,7,9},{3,6,7,11},{3,6,8,9},{3,6,8,11},{3,6,9,11},{3,7,8,9},{3,7,8,11},{3,7,9,11},{6,7,8,9},{6,8,9,11}]

theorem dual_actual (halph : AlphabetComplete link47 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link47 Q := by
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

theorem all_foursets (halph : AlphabetComplete link47 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link47 Q :=
  class_census link47 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source47
