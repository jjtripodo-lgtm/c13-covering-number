import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source21
import C13Global.FastGroups.Source21Part00
import C13Global.FastGroups.Source21Part01
import C13Global.FastGroups.Source21Part02
import C13Global.FastGroups.Source21Part03
namespace C13.Global.Relative.Source21
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source21
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link21 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link21 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link21 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link21 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_000.pointList FastDual21_000.columns FastDual21_000.rows FastDual21_000.bound (by decide +kernel)
    FastDual21_000.column_mask FastDual21_000.checked hc F hF hroot hmin hout

theorem query216 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {1,3,6,9} := rep000 halph

theorem rep001 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_001.pointList FastDual21_001.columns FastDual21_001.rows FastDual21_001.bound (by decide +kernel)
    FastDual21_001.column_mask FastDual21_001.checked hc F hF hroot hmin hout

theorem query217 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {1,3,6,10} := rep001 halph

theorem rep002 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_002.pointList FastDual21_002.columns FastDual21_002.rows FastDual21_002.bound (by decide +kernel)
    FastDual21_002.column_mask FastDual21_002.checked hc F hF hroot hmin hout

theorem query218 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {1,3,6,11} := rep002 halph

theorem rep003 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_003.pointList FastDual21_003.columns FastDual21_003.rows FastDual21_003.bound (by decide +kernel)
    FastDual21_003.column_mask FastDual21_003.checked hc F hF hroot hmin hout

theorem query220 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {1,3,7,9} := rep003 halph

theorem rep004 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_004.pointList FastDual21_004.columns FastDual21_004.rows FastDual21_004.bound (by decide +kernel)
    FastDual21_004.column_mask FastDual21_004.checked hc F hF hroot hmin hout

theorem query221 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {1,3,7,10} := rep004 halph

theorem rep005 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_005.pointList FastDual21_005.columns FastDual21_005.rows FastDual21_005.bound (by decide +kernel)
    FastDual21_005.column_mask FastDual21_005.checked hc F hF hroot hmin hout

theorem query222 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {1,3,7,11} := rep005 halph

theorem rep006 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_006.pointList FastDual21_006.columns FastDual21_006.rows FastDual21_006.bound (by decide +kernel)
    FastDual21_006.column_mask FastDual21_006.checked hc F hF hroot hmin hout

theorem query227 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {1,3,9,11} := rep006 halph

theorem rep007 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_007.pointList FastDual21_007.columns FastDual21_007.rows FastDual21_007.bound (by decide +kernel)
    FastDual21_007.column_mask FastDual21_007.checked hc F hF hroot hmin hout

theorem query266 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {1,6,7,9} := rep007 halph

theorem rep008 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_008.pointList FastDual21_008.columns FastDual21_008.rows FastDual21_008.bound (by decide +kernel)
    FastDual21_008.column_mask FastDual21_008.checked hc F hF hroot hmin hout

theorem query267 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {1,6,7,10} := rep008 halph

theorem rep009 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_009.pointList FastDual21_009.columns FastDual21_009.rows FastDual21_009.bound (by decide +kernel)
    FastDual21_009.column_mask FastDual21_009.checked hc F hF hroot hmin hout

theorem query268 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {1,6,7,11} := rep009 halph

theorem rep010 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_010.pointList FastDual21_010.columns FastDual21_010.rows FastDual21_010.bound (by decide +kernel)
    FastDual21_010.column_mask FastDual21_010.checked hc F hF hroot hmin hout

theorem query272 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {1,6,9,10} := rep010 halph

theorem rep011 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_011.pointList FastDual21_011.columns FastDual21_011.rows FastDual21_011.bound (by decide +kernel)
    FastDual21_011.column_mask FastDual21_011.checked hc F hF hroot hmin hout

theorem query273 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {1,6,9,11} := rep011 halph

theorem rep012 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_012.pointList FastDual21_012.columns FastDual21_012.rows FastDual21_012.bound (by decide +kernel)
    FastDual21_012.column_mask FastDual21_012.checked hc F hF hroot hmin hout

theorem query274 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {1,6,10,11} := rep012 halph

theorem rep013 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_013.pointList FastDual21_013.columns FastDual21_013.rows FastDual21_013.bound (by decide +kernel)
    FastDual21_013.column_mask FastDual21_013.checked hc F hF hroot hmin hout

theorem query278 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {1,7,9,10} := rep013 halph

theorem rep014 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_014.pointList FastDual21_014.columns FastDual21_014.rows FastDual21_014.bound (by decide +kernel)
    FastDual21_014.column_mask FastDual21_014.checked hc F hF hroot hmin hout

theorem query279 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {1,7,9,11} := rep014 halph

theorem rep015 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_015.pointList FastDual21_015.columns FastDual21_015.rows FastDual21_015.bound (by decide +kernel)
    FastDual21_015.column_mask FastDual21_015.checked hc F hF hroot hmin hout

theorem query280 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {1,7,10,11} := rep015 halph

theorem rep016 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_016.pointList FastDual21_016.columns FastDual21_016.rows FastDual21_016.bound (by decide +kernel)
    FastDual21_016.column_mask FastDual21_016.checked hc F hF hroot hmin hout

theorem query406 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {3,6,7,9} := rep016 halph

theorem rep017 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_017.pointList FastDual21_017.columns FastDual21_017.rows FastDual21_017.bound (by decide +kernel)
    FastDual21_017.column_mask FastDual21_017.checked hc F hF hroot hmin hout

theorem query407 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {3,6,7,10} := rep017 halph

theorem rep018 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_018.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_018.pointList FastDual21_018.columns FastDual21_018.rows FastDual21_018.bound (by decide +kernel)
    FastDual21_018.column_mask FastDual21_018.checked hc F hF hroot hmin hout

theorem query408 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {3,6,7,11} := rep018 halph

theorem rep019 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_019.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_019.pointList FastDual21_019.columns FastDual21_019.rows FastDual21_019.bound (by decide +kernel)
    FastDual21_019.column_mask FastDual21_019.checked hc F hF hroot hmin hout

theorem query412 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {3,6,9,10} := rep019 halph

theorem rep020 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_020.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_020.pointList FastDual21_020.columns FastDual21_020.rows FastDual21_020.bound (by decide +kernel)
    FastDual21_020.column_mask FastDual21_020.checked hc F hF hroot hmin hout

theorem query413 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {3,6,9,11} := rep020 halph

theorem rep021 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_021.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_021.pointList FastDual21_021.columns FastDual21_021.rows FastDual21_021.bound (by decide +kernel)
    FastDual21_021.column_mask FastDual21_021.checked hc F hF hroot hmin hout

theorem query414 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {3,6,10,11} := rep021 halph

theorem rep022 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_022.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_022.pointList FastDual21_022.columns FastDual21_022.rows FastDual21_022.bound (by decide +kernel)
    FastDual21_022.column_mask FastDual21_022.checked hc F hF hroot hmin hout

theorem query418 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {3,7,9,10} := rep022 halph

theorem rep023 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_023.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_023.pointList FastDual21_023.columns FastDual21_023.rows FastDual21_023.bound (by decide +kernel)
    FastDual21_023.column_mask FastDual21_023.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {3,7,9,11} := rep023 halph

theorem rep024 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_024.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_024.pointList FastDual21_024.columns FastDual21_024.rows FastDual21_024.bound (by decide +kernel)
    FastDual21_024.column_mask FastDual21_024.checked hc F hF hroot hmin hout

theorem query420 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {3,7,10,11} := rep024 halph

theorem rep025 (halph : AlphabetComplete link21 alphabets) :
    ActualObstruction link21 FastDual21_025.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link21 rootCodes root_binding alphabets halph nonincident_complete
    FastDual21_025.pointList FastDual21_025.columns FastDual21_025.rows FastDual21_025.bound (by decide +kernel)
    FastDual21_025.column_mask FastDual21_025.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link21 alphabets) : ActualObstruction link21 {6,7,10,11} := rep025 halph

def dualQuads : List (Finset Point) := [{1,3,6,9},{1,3,6,10},{1,3,6,11},{1,3,7,9},{1,3,7,10},{1,3,7,11},{1,3,9,11},{1,6,7,9},{1,6,7,10},{1,6,7,11},{1,6,9,10},{1,6,9,11},{1,6,10,11},{1,7,9,10},{1,7,9,11},{1,7,10,11},{3,6,7,9},{3,6,7,10},{3,6,7,11},{3,6,9,10},{3,6,9,11},{3,6,10,11},{3,7,9,10},{3,7,9,11},{3,7,10,11},{6,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link21 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link21 Q := by
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

theorem all_foursets (halph : AlphabetComplete link21 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link21 Q :=
  class_census link21 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source21
