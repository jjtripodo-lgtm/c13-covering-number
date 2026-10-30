import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source43
import C13Global.FastGroups.Source43Part00
import C13Global.FastGroups.Source43Part01
import C13Global.FastGroups.Source43Part02
import C13Global.FastGroups.Source43Part03
namespace C13.Global.Relative.Source43
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source43
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link43 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link43 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link43 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link43 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_000.pointList FastDual43_000.columns FastDual43_000.rows FastDual43_000.bound (by decide +kernel)
    FastDual43_000.column_mask FastDual43_000.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,3,6,7} := rep000 halph

theorem rep001 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_001.pointList FastDual43_001.columns FastDual43_001.rows FastDual43_001.bound (by decide +kernel)
    FastDual43_001.column_mask FastDual43_001.checked hc F hF hroot hmin hout

theorem query299 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,3,6,8} := rep001 halph

theorem rep002 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_002.pointList FastDual43_002.columns FastDual43_002.rows FastDual43_002.bound (by decide +kernel)
    FastDual43_002.column_mask FastDual43_002.checked hc F hF hroot hmin hout

theorem query300 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,3,6,9} := rep002 halph

theorem rep003 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_003.pointList FastDual43_003.columns FastDual43_003.rows FastDual43_003.bound (by decide +kernel)
    FastDual43_003.column_mask FastDual43_003.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,3,6,11} := rep003 halph

theorem rep004 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_004.pointList FastDual43_004.columns FastDual43_004.rows FastDual43_004.bound (by decide +kernel)
    FastDual43_004.column_mask FastDual43_004.checked hc F hF hroot hmin hout

theorem query303 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,3,7,8} := rep004 halph

theorem rep005 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_005.pointList FastDual43_005.columns FastDual43_005.rows FastDual43_005.bound (by decide +kernel)
    FastDual43_005.column_mask FastDual43_005.checked hc F hF hroot hmin hout

theorem query304 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,3,7,9} := rep005 halph

theorem rep006 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_006.pointList FastDual43_006.columns FastDual43_006.rows FastDual43_006.bound (by decide +kernel)
    FastDual43_006.column_mask FastDual43_006.checked hc F hF hroot hmin hout

theorem query306 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,3,7,11} := rep006 halph

theorem rep007 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_007.pointList FastDual43_007.columns FastDual43_007.rows FastDual43_007.bound (by decide +kernel)
    FastDual43_007.column_mask FastDual43_007.checked hc F hF hroot hmin hout

theorem query307 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,3,8,9} := rep007 halph

theorem rep008 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_008.pointList FastDual43_008.columns FastDual43_008.rows FastDual43_008.bound (by decide +kernel)
    FastDual43_008.column_mask FastDual43_008.checked hc F hF hroot hmin hout

theorem query349 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,6,7,8} := rep008 halph

theorem rep009 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_009.pointList FastDual43_009.columns FastDual43_009.rows FastDual43_009.bound (by decide +kernel)
    FastDual43_009.column_mask FastDual43_009.checked hc F hF hroot hmin hout

theorem query350 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,6,7,9} := rep009 halph

theorem rep010 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_010.pointList FastDual43_010.columns FastDual43_010.rows FastDual43_010.bound (by decide +kernel)
    FastDual43_010.column_mask FastDual43_010.checked hc F hF hroot hmin hout

theorem query352 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,6,7,11} := rep010 halph

theorem rep011 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_011.pointList FastDual43_011.columns FastDual43_011.rows FastDual43_011.bound (by decide +kernel)
    FastDual43_011.column_mask FastDual43_011.checked hc F hF hroot hmin hout

theorem query353 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,6,8,9} := rep011 halph

theorem rep012 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_012.pointList FastDual43_012.columns FastDual43_012.rows FastDual43_012.bound (by decide +kernel)
    FastDual43_012.column_mask FastDual43_012.checked hc F hF hroot hmin hout

theorem query355 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,6,8,11} := rep012 halph

theorem rep013 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_013.pointList FastDual43_013.columns FastDual43_013.rows FastDual43_013.bound (by decide +kernel)
    FastDual43_013.column_mask FastDual43_013.checked hc F hF hroot hmin hout

theorem query357 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,6,9,11} := rep013 halph

theorem rep014 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_014.pointList FastDual43_014.columns FastDual43_014.rows FastDual43_014.bound (by decide +kernel)
    FastDual43_014.column_mask FastDual43_014.checked hc F hF hroot hmin hout

theorem query359 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,7,8,9} := rep014 halph

theorem rep015 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_015.pointList FastDual43_015.columns FastDual43_015.rows FastDual43_015.bound (by decide +kernel)
    FastDual43_015.column_mask FastDual43_015.checked hc F hF hroot hmin hout

theorem query361 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,7,8,11} := rep015 halph

theorem rep016 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_016.pointList FastDual43_016.columns FastDual43_016.rows FastDual43_016.bound (by decide +kernel)
    FastDual43_016.column_mask FastDual43_016.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {2,7,9,11} := rep016 halph

theorem rep017 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_017.pointList FastDual43_017.columns FastDual43_017.rows FastDual43_017.bound (by decide +kernel)
    FastDual43_017.column_mask FastDual43_017.checked hc F hF hroot hmin hout

theorem query405 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {3,6,7,8} := rep017 halph

theorem rep018 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_018.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_018.pointList FastDual43_018.columns FastDual43_018.rows FastDual43_018.bound (by decide +kernel)
    FastDual43_018.column_mask FastDual43_018.checked hc F hF hroot hmin hout

theorem query406 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {3,6,7,9} := rep018 halph

theorem rep019 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_019.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_019.pointList FastDual43_019.columns FastDual43_019.rows FastDual43_019.bound (by decide +kernel)
    FastDual43_019.column_mask FastDual43_019.checked hc F hF hroot hmin hout

theorem query408 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {3,6,7,11} := rep019 halph

theorem rep020 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_020.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_020.pointList FastDual43_020.columns FastDual43_020.rows FastDual43_020.bound (by decide +kernel)
    FastDual43_020.column_mask FastDual43_020.checked hc F hF hroot hmin hout

theorem query409 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {3,6,8,9} := rep020 halph

theorem rep021 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_021.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_021.pointList FastDual43_021.columns FastDual43_021.rows FastDual43_021.bound (by decide +kernel)
    FastDual43_021.column_mask FastDual43_021.checked hc F hF hroot hmin hout

theorem query411 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {3,6,8,11} := rep021 halph

theorem rep022 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_022.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_022.pointList FastDual43_022.columns FastDual43_022.rows FastDual43_022.bound (by decide +kernel)
    FastDual43_022.column_mask FastDual43_022.checked hc F hF hroot hmin hout

theorem query413 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {3,6,9,11} := rep022 halph

theorem rep023 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_023.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_023.pointList FastDual43_023.columns FastDual43_023.rows FastDual43_023.bound (by decide +kernel)
    FastDual43_023.column_mask FastDual43_023.checked hc F hF hroot hmin hout

theorem query415 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {3,7,8,9} := rep023 halph

theorem rep024 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_024.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_024.pointList FastDual43_024.columns FastDual43_024.rows FastDual43_024.bound (by decide +kernel)
    FastDual43_024.column_mask FastDual43_024.checked hc F hF hroot hmin hout

theorem query417 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {3,7,8,11} := rep024 halph

theorem rep025 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_025.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_025.pointList FastDual43_025.columns FastDual43_025.rows FastDual43_025.bound (by decide +kernel)
    FastDual43_025.column_mask FastDual43_025.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {3,7,9,11} := rep025 halph

theorem rep026 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_026.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_026.pointList FastDual43_026.columns FastDual43_026.rows FastDual43_026.bound (by decide +kernel)
    FastDual43_026.column_mask FastDual43_026.checked hc F hF hroot hmin hout

theorem query480 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {6,7,8,9} := rep026 halph

theorem rep027 (halph : AlphabetComplete link43 alphabets) :
    ActualObstruction link43 FastDual43_027.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link43 rootCodes root_binding alphabets halph nonincident_complete
    FastDual43_027.pointList FastDual43_027.columns FastDual43_027.rows FastDual43_027.bound (by decide +kernel)
    FastDual43_027.column_mask FastDual43_027.checked hc F hF hroot hmin hout

theorem query487 (halph : AlphabetComplete link43 alphabets) : ActualObstruction link43 {6,8,9,11} := rep027 halph

def dualQuads : List (Finset Point) := [{2,3,6,7},{2,3,6,8},{2,3,6,9},{2,3,6,11},{2,3,7,8},{2,3,7,9},{2,3,7,11},{2,3,8,9},{2,6,7,8},{2,6,7,9},{2,6,7,11},{2,6,8,9},{2,6,8,11},{2,6,9,11},{2,7,8,9},{2,7,8,11},{2,7,9,11},{3,6,7,8},{3,6,7,9},{3,6,7,11},{3,6,8,9},{3,6,8,11},{3,6,9,11},{3,7,8,9},{3,7,8,11},{3,7,9,11},{6,7,8,9},{6,8,9,11}]

theorem dual_actual (halph : AlphabetComplete link43 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link43 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query298 halph
  · exact query299 halph
  · exact query300 halph
  · exact query302 halph
  · exact query303 halph
  · exact query304 halph
  · exact query306 halph
  · exact query307 halph
  · exact query349 halph
  · exact query350 halph
  · exact query352 halph
  · exact query353 halph
  · exact query355 halph
  · exact query357 halph
  · exact query359 halph
  · exact query361 halph
  · exact query363 halph
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

theorem all_foursets (halph : AlphabetComplete link43 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link43 Q :=
  class_census link43 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source43
