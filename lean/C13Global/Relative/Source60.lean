import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source60
import C13Global.FastGroups.Source60Part00
import C13Global.FastGroups.Source60Part01
import C13Global.FastGroups.Source60Part02
import C13Global.FastGroups.Source60Part03
namespace C13.Global.Relative.Source60
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source60
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link60 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link60 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link60 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link60 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_000.pointList FastDual60_000.columns FastDual60_000.rows FastDual60_000.bound (by decide +kernel)
    FastDual60_000.column_mask FastDual60_000.checked hc F hF hroot hmin hout

theorem query209 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {1,3,5,7} := rep000 halph

theorem rep001 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_001.pointList FastDual60_001.columns FastDual60_001.rows FastDual60_001.bound (by decide +kernel)
    FastDual60_001.column_mask FastDual60_001.checked hc F hF hroot hmin hout

theorem query212 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {1,3,5,10} := rep001 halph

theorem rep002 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_002.pointList FastDual60_002.columns FastDual60_002.rows FastDual60_002.bound (by decide +kernel)
    FastDual60_002.column_mask FastDual60_002.checked hc F hF hroot hmin hout

theorem query213 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {1,3,5,11} := rep002 halph

theorem rep003 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_003.pointList FastDual60_003.columns FastDual60_003.rows FastDual60_003.bound (by decide +kernel)
    FastDual60_003.column_mask FastDual60_003.checked hc F hF hroot hmin hout

theorem query217 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {1,3,6,10} := rep003 halph

theorem rep004 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_004.pointList FastDual60_004.columns FastDual60_004.rows FastDual60_004.bound (by decide +kernel)
    FastDual60_004.column_mask FastDual60_004.checked hc F hF hroot hmin hout

theorem query218 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {1,3,6,11} := rep004 halph

theorem rep005 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_005.pointList FastDual60_005.columns FastDual60_005.rows FastDual60_005.bound (by decide +kernel)
    FastDual60_005.column_mask FastDual60_005.checked hc F hF hroot hmin hout

theorem query221 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {1,3,7,10} := rep005 halph

theorem rep006 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_006.pointList FastDual60_006.columns FastDual60_006.rows FastDual60_006.bound (by decide +kernel)
    FastDual60_006.column_mask FastDual60_006.checked hc F hF hroot hmin hout

theorem query222 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {1,3,7,11} := rep006 halph

theorem rep007 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_007.pointList FastDual60_007.columns FastDual60_007.rows FastDual60_007.bound (by decide +kernel)
    FastDual60_007.column_mask FastDual60_007.checked hc F hF hroot hmin hout

theorem query253 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {1,5,6,10} := rep007 halph

theorem rep008 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_008.pointList FastDual60_008.columns FastDual60_008.rows FastDual60_008.bound (by decide +kernel)
    FastDual60_008.column_mask FastDual60_008.checked hc F hF hroot hmin hout

theorem query254 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {1,5,6,11} := rep008 halph

theorem rep009 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_009.pointList FastDual60_009.columns FastDual60_009.rows FastDual60_009.bound (by decide +kernel)
    FastDual60_009.column_mask FastDual60_009.checked hc F hF hroot hmin hout

theorem query257 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {1,5,7,10} := rep009 halph

theorem rep010 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_010.pointList FastDual60_010.columns FastDual60_010.rows FastDual60_010.bound (by decide +kernel)
    FastDual60_010.column_mask FastDual60_010.checked hc F hF hroot hmin hout

theorem query258 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {1,5,7,11} := rep010 halph

theorem rep011 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_011.pointList FastDual60_011.columns FastDual60_011.rows FastDual60_011.bound (by decide +kernel)
    FastDual60_011.column_mask FastDual60_011.checked hc F hF hroot hmin hout

theorem query264 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {1,5,10,11} := rep011 halph

theorem rep012 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_012.pointList FastDual60_012.columns FastDual60_012.rows FastDual60_012.bound (by decide +kernel)
    FastDual60_012.column_mask FastDual60_012.checked hc F hF hroot hmin hout

theorem query267 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {1,6,7,10} := rep012 halph

theorem rep013 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_013.pointList FastDual60_013.columns FastDual60_013.rows FastDual60_013.bound (by decide +kernel)
    FastDual60_013.column_mask FastDual60_013.checked hc F hF hroot hmin hout

theorem query268 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {1,6,7,11} := rep013 halph

theorem rep014 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_014.pointList FastDual60_014.columns FastDual60_014.rows FastDual60_014.bound (by decide +kernel)
    FastDual60_014.column_mask FastDual60_014.checked hc F hF hroot hmin hout

theorem query274 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {1,6,10,11} := rep014 halph

theorem rep015 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_015.pointList FastDual60_015.columns FastDual60_015.rows FastDual60_015.bound (by decide +kernel)
    FastDual60_015.column_mask FastDual60_015.checked hc F hF hroot hmin hout

theorem query280 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {1,7,10,11} := rep015 halph

theorem rep016 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_016.pointList FastDual60_016.columns FastDual60_016.rows FastDual60_016.bound (by decide +kernel)
    FastDual60_016.column_mask FastDual60_016.checked hc F hF hroot hmin hout

theorem query393 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {3,5,6,10} := rep016 halph

theorem rep017 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_017.pointList FastDual60_017.columns FastDual60_017.rows FastDual60_017.bound (by decide +kernel)
    FastDual60_017.column_mask FastDual60_017.checked hc F hF hroot hmin hout

theorem query394 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {3,5,6,11} := rep017 halph

theorem rep018 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_018.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_018.pointList FastDual60_018.columns FastDual60_018.rows FastDual60_018.bound (by decide +kernel)
    FastDual60_018.column_mask FastDual60_018.checked hc F hF hroot hmin hout

theorem query397 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {3,5,7,10} := rep018 halph

theorem rep019 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_019.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_019.pointList FastDual60_019.columns FastDual60_019.rows FastDual60_019.bound (by decide +kernel)
    FastDual60_019.column_mask FastDual60_019.checked hc F hF hroot hmin hout

theorem query398 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {3,5,7,11} := rep019 halph

theorem rep020 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_020.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_020.pointList FastDual60_020.columns FastDual60_020.rows FastDual60_020.bound (by decide +kernel)
    FastDual60_020.column_mask FastDual60_020.checked hc F hF hroot hmin hout

theorem query404 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {3,5,10,11} := rep020 halph

theorem rep021 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_021.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_021.pointList FastDual60_021.columns FastDual60_021.rows FastDual60_021.bound (by decide +kernel)
    FastDual60_021.column_mask FastDual60_021.checked hc F hF hroot hmin hout

theorem query407 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {3,6,7,10} := rep021 halph

theorem rep022 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_022.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_022.pointList FastDual60_022.columns FastDual60_022.rows FastDual60_022.bound (by decide +kernel)
    FastDual60_022.column_mask FastDual60_022.checked hc F hF hroot hmin hout

theorem query408 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {3,6,7,11} := rep022 halph

theorem rep023 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_023.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_023.pointList FastDual60_023.columns FastDual60_023.rows FastDual60_023.bound (by decide +kernel)
    FastDual60_023.column_mask FastDual60_023.checked hc F hF hroot hmin hout

theorem query414 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {3,6,10,11} := rep023 halph

theorem rep024 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_024.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_024.pointList FastDual60_024.columns FastDual60_024.rows FastDual60_024.bound (by decide +kernel)
    FastDual60_024.column_mask FastDual60_024.checked hc F hF hroot hmin hout

theorem query420 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {3,7,10,11} := rep024 halph

theorem rep025 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_025.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_025.pointList FastDual60_025.columns FastDual60_025.rows FastDual60_025.bound (by decide +kernel)
    FastDual60_025.column_mask FastDual60_025.checked hc F hF hroot hmin hout

theorem query462 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {5,6,7,10} := rep025 halph

theorem rep026 (halph : AlphabetComplete link60 alphabets) :
    ActualObstruction link60 FastDual60_026.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link60 rootCodes root_binding alphabets halph nonincident_complete
    FastDual60_026.pointList FastDual60_026.columns FastDual60_026.rows FastDual60_026.bound (by decide +kernel)
    FastDual60_026.column_mask FastDual60_026.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link60 alphabets) : ActualObstruction link60 {6,7,10,11} := rep026 halph

def dualQuads : List (Finset Point) := [{1,3,5,7},{1,3,5,10},{1,3,5,11},{1,3,6,10},{1,3,6,11},{1,3,7,10},{1,3,7,11},{1,5,6,10},{1,5,6,11},{1,5,7,10},{1,5,7,11},{1,5,10,11},{1,6,7,10},{1,6,7,11},{1,6,10,11},{1,7,10,11},{3,5,6,10},{3,5,6,11},{3,5,7,10},{3,5,7,11},{3,5,10,11},{3,6,7,10},{3,6,7,11},{3,6,10,11},{3,7,10,11},{5,6,7,10},{6,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link60 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link60 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query209 halph
  · exact query212 halph
  · exact query213 halph
  · exact query217 halph
  · exact query218 halph
  · exact query221 halph
  · exact query222 halph
  · exact query253 halph
  · exact query254 halph
  · exact query257 halph
  · exact query258 halph
  · exact query264 halph
  · exact query267 halph
  · exact query268 halph
  · exact query274 halph
  · exact query280 halph
  · exact query393 halph
  · exact query394 halph
  · exact query397 halph
  · exact query398 halph
  · exact query404 halph
  · exact query407 halph
  · exact query408 halph
  · exact query414 halph
  · exact query420 halph
  · exact query462 halph
  · exact query485 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link60 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link60 Q :=
  class_census link60 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source60
