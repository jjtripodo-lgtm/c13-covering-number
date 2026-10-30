import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source32
import C13Global.FastGroups.Source32Part00
import C13Global.FastGroups.Source32Part01
import C13Global.FastGroups.Source32Part02
import C13Global.FastGroups.Source32Part03
namespace C13.Global.Relative.Source32
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source32
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link32 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link32 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link32 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link32 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_000.pointList FastDual32_000.columns FastDual32_000.rows FastDual32_000.bound (by decide +kernel)
    FastDual32_000.column_mask FastDual32_000.checked hc F hF hroot hmin hout

theorem query216 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {1,3,6,9} := rep000 halph

theorem rep001 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_001.pointList FastDual32_001.columns FastDual32_001.rows FastDual32_001.bound (by decide +kernel)
    FastDual32_001.column_mask FastDual32_001.checked hc F hF hroot hmin hout

theorem query217 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {1,3,6,10} := rep001 halph

theorem rep002 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_002.pointList FastDual32_002.columns FastDual32_002.rows FastDual32_002.bound (by decide +kernel)
    FastDual32_002.column_mask FastDual32_002.checked hc F hF hroot hmin hout

theorem query218 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {1,3,6,11} := rep002 halph

theorem rep003 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_003.pointList FastDual32_003.columns FastDual32_003.rows FastDual32_003.bound (by decide +kernel)
    FastDual32_003.column_mask FastDual32_003.checked hc F hF hroot hmin hout

theorem query220 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {1,3,7,9} := rep003 halph

theorem rep004 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_004.pointList FastDual32_004.columns FastDual32_004.rows FastDual32_004.bound (by decide +kernel)
    FastDual32_004.column_mask FastDual32_004.checked hc F hF hroot hmin hout

theorem query221 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {1,3,7,10} := rep004 halph

theorem rep005 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_005.pointList FastDual32_005.columns FastDual32_005.rows FastDual32_005.bound (by decide +kernel)
    FastDual32_005.column_mask FastDual32_005.checked hc F hF hroot hmin hout

theorem query222 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {1,3,7,11} := rep005 halph

theorem rep006 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_006.pointList FastDual32_006.columns FastDual32_006.rows FastDual32_006.bound (by decide +kernel)
    FastDual32_006.column_mask FastDual32_006.checked hc F hF hroot hmin hout

theorem query227 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {1,3,9,11} := rep006 halph

theorem rep007 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_007.pointList FastDual32_007.columns FastDual32_007.rows FastDual32_007.bound (by decide +kernel)
    FastDual32_007.column_mask FastDual32_007.checked hc F hF hroot hmin hout

theorem query266 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {1,6,7,9} := rep007 halph

theorem rep008 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_008.pointList FastDual32_008.columns FastDual32_008.rows FastDual32_008.bound (by decide +kernel)
    FastDual32_008.column_mask FastDual32_008.checked hc F hF hroot hmin hout

theorem query267 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {1,6,7,10} := rep008 halph

theorem rep009 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_009.pointList FastDual32_009.columns FastDual32_009.rows FastDual32_009.bound (by decide +kernel)
    FastDual32_009.column_mask FastDual32_009.checked hc F hF hroot hmin hout

theorem query268 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {1,6,7,11} := rep009 halph

theorem rep010 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_010.pointList FastDual32_010.columns FastDual32_010.rows FastDual32_010.bound (by decide +kernel)
    FastDual32_010.column_mask FastDual32_010.checked hc F hF hroot hmin hout

theorem query272 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {1,6,9,10} := rep010 halph

theorem rep011 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_011.pointList FastDual32_011.columns FastDual32_011.rows FastDual32_011.bound (by decide +kernel)
    FastDual32_011.column_mask FastDual32_011.checked hc F hF hroot hmin hout

theorem query273 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {1,6,9,11} := rep011 halph

theorem rep012 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_012.pointList FastDual32_012.columns FastDual32_012.rows FastDual32_012.bound (by decide +kernel)
    FastDual32_012.column_mask FastDual32_012.checked hc F hF hroot hmin hout

theorem query274 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {1,6,10,11} := rep012 halph

theorem rep013 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_013.pointList FastDual32_013.columns FastDual32_013.rows FastDual32_013.bound (by decide +kernel)
    FastDual32_013.column_mask FastDual32_013.checked hc F hF hroot hmin hout

theorem query278 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {1,7,9,10} := rep013 halph

theorem rep014 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_014.pointList FastDual32_014.columns FastDual32_014.rows FastDual32_014.bound (by decide +kernel)
    FastDual32_014.column_mask FastDual32_014.checked hc F hF hroot hmin hout

theorem query279 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {1,7,9,11} := rep014 halph

theorem rep015 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_015.pointList FastDual32_015.columns FastDual32_015.rows FastDual32_015.bound (by decide +kernel)
    FastDual32_015.column_mask FastDual32_015.checked hc F hF hroot hmin hout

theorem query280 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {1,7,10,11} := rep015 halph

theorem rep016 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_016.pointList FastDual32_016.columns FastDual32_016.rows FastDual32_016.bound (by decide +kernel)
    FastDual32_016.column_mask FastDual32_016.checked hc F hF hroot hmin hout

theorem query406 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {3,6,7,9} := rep016 halph

theorem rep017 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_017.pointList FastDual32_017.columns FastDual32_017.rows FastDual32_017.bound (by decide +kernel)
    FastDual32_017.column_mask FastDual32_017.checked hc F hF hroot hmin hout

theorem query407 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {3,6,7,10} := rep017 halph

theorem rep018 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_018.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_018.pointList FastDual32_018.columns FastDual32_018.rows FastDual32_018.bound (by decide +kernel)
    FastDual32_018.column_mask FastDual32_018.checked hc F hF hroot hmin hout

theorem query408 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {3,6,7,11} := rep018 halph

theorem rep019 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_019.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_019.pointList FastDual32_019.columns FastDual32_019.rows FastDual32_019.bound (by decide +kernel)
    FastDual32_019.column_mask FastDual32_019.checked hc F hF hroot hmin hout

theorem query412 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {3,6,9,10} := rep019 halph

theorem rep020 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_020.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_020.pointList FastDual32_020.columns FastDual32_020.rows FastDual32_020.bound (by decide +kernel)
    FastDual32_020.column_mask FastDual32_020.checked hc F hF hroot hmin hout

theorem query413 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {3,6,9,11} := rep020 halph

theorem rep021 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_021.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_021.pointList FastDual32_021.columns FastDual32_021.rows FastDual32_021.bound (by decide +kernel)
    FastDual32_021.column_mask FastDual32_021.checked hc F hF hroot hmin hout

theorem query414 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {3,6,10,11} := rep021 halph

theorem rep022 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_022.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_022.pointList FastDual32_022.columns FastDual32_022.rows FastDual32_022.bound (by decide +kernel)
    FastDual32_022.column_mask FastDual32_022.checked hc F hF hroot hmin hout

theorem query418 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {3,7,9,10} := rep022 halph

theorem rep023 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_023.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_023.pointList FastDual32_023.columns FastDual32_023.rows FastDual32_023.bound (by decide +kernel)
    FastDual32_023.column_mask FastDual32_023.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {3,7,9,11} := rep023 halph

theorem rep024 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_024.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_024.pointList FastDual32_024.columns FastDual32_024.rows FastDual32_024.bound (by decide +kernel)
    FastDual32_024.column_mask FastDual32_024.checked hc F hF hroot hmin hout

theorem query420 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {3,7,10,11} := rep024 halph

theorem rep025 (halph : AlphabetComplete link32 alphabets) :
    ActualObstruction link32 FastDual32_025.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link32 rootCodes root_binding alphabets halph nonincident_complete
    FastDual32_025.pointList FastDual32_025.columns FastDual32_025.rows FastDual32_025.bound (by decide +kernel)
    FastDual32_025.column_mask FastDual32_025.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link32 alphabets) : ActualObstruction link32 {6,7,10,11} := rep025 halph

def dualQuads : List (Finset Point) := [{1,3,6,9},{1,3,6,10},{1,3,6,11},{1,3,7,9},{1,3,7,10},{1,3,7,11},{1,3,9,11},{1,6,7,9},{1,6,7,10},{1,6,7,11},{1,6,9,10},{1,6,9,11},{1,6,10,11},{1,7,9,10},{1,7,9,11},{1,7,10,11},{3,6,7,9},{3,6,7,10},{3,6,7,11},{3,6,9,10},{3,6,9,11},{3,6,10,11},{3,7,9,10},{3,7,9,11},{3,7,10,11},{6,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link32 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link32 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query216 halph
  · exact query217 halph
  · exact query218 halph
  · exact query220 halph
  · exact query221 halph
  · exact query222 halph
  · exact query227 halph
  · exact query266 halph
  · exact query267 halph
  · exact query268 halph
  · exact query272 halph
  · exact query273 halph
  · exact query274 halph
  · exact query278 halph
  · exact query279 halph
  · exact query280 halph
  · exact query406 halph
  · exact query407 halph
  · exact query408 halph
  · exact query412 halph
  · exact query413 halph
  · exact query414 halph
  · exact query418 halph
  · exact query419 halph
  · exact query420 halph
  · exact query485 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link32 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link32 Q :=
  class_census link32 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source32
