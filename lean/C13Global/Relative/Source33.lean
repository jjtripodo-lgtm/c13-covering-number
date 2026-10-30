import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source33
import C13Global.FastGroups.Source33Part00
import C13Global.FastGroups.Source33Part01
import C13Global.FastGroups.Source33Part02
import C13Global.FastGroups.Source33Part03
namespace C13.Global.Relative.Source33
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source33
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link33 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link33 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link33 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link33 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_000.pointList FastDual33_000.columns FastDual33_000.rows FastDual33_000.bound (by decide +kernel)
    FastDual33_000.column_mask FastDual33_000.checked hc F hF hroot hmin hout

theorem query216 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {1,3,6,9} := rep000 halph

theorem rep001 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_001.pointList FastDual33_001.columns FastDual33_001.rows FastDual33_001.bound (by decide +kernel)
    FastDual33_001.column_mask FastDual33_001.checked hc F hF hroot hmin hout

theorem query217 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {1,3,6,10} := rep001 halph

theorem rep002 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_002.pointList FastDual33_002.columns FastDual33_002.rows FastDual33_002.bound (by decide +kernel)
    FastDual33_002.column_mask FastDual33_002.checked hc F hF hroot hmin hout

theorem query218 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {1,3,6,11} := rep002 halph

theorem rep003 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_003.pointList FastDual33_003.columns FastDual33_003.rows FastDual33_003.bound (by decide +kernel)
    FastDual33_003.column_mask FastDual33_003.checked hc F hF hroot hmin hout

theorem query220 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {1,3,7,9} := rep003 halph

theorem rep004 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_004.pointList FastDual33_004.columns FastDual33_004.rows FastDual33_004.bound (by decide +kernel)
    FastDual33_004.column_mask FastDual33_004.checked hc F hF hroot hmin hout

theorem query221 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {1,3,7,10} := rep004 halph

theorem rep005 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_005.pointList FastDual33_005.columns FastDual33_005.rows FastDual33_005.bound (by decide +kernel)
    FastDual33_005.column_mask FastDual33_005.checked hc F hF hroot hmin hout

theorem query222 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {1,3,7,11} := rep005 halph

theorem rep006 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_006.pointList FastDual33_006.columns FastDual33_006.rows FastDual33_006.bound (by decide +kernel)
    FastDual33_006.column_mask FastDual33_006.checked hc F hF hroot hmin hout

theorem query227 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {1,3,9,11} := rep006 halph

theorem rep007 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_007.pointList FastDual33_007.columns FastDual33_007.rows FastDual33_007.bound (by decide +kernel)
    FastDual33_007.column_mask FastDual33_007.checked hc F hF hroot hmin hout

theorem query266 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {1,6,7,9} := rep007 halph

theorem rep008 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_008.pointList FastDual33_008.columns FastDual33_008.rows FastDual33_008.bound (by decide +kernel)
    FastDual33_008.column_mask FastDual33_008.checked hc F hF hroot hmin hout

theorem query267 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {1,6,7,10} := rep008 halph

theorem rep009 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_009.pointList FastDual33_009.columns FastDual33_009.rows FastDual33_009.bound (by decide +kernel)
    FastDual33_009.column_mask FastDual33_009.checked hc F hF hroot hmin hout

theorem query268 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {1,6,7,11} := rep009 halph

theorem rep010 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_010.pointList FastDual33_010.columns FastDual33_010.rows FastDual33_010.bound (by decide +kernel)
    FastDual33_010.column_mask FastDual33_010.checked hc F hF hroot hmin hout

theorem query272 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {1,6,9,10} := rep010 halph

theorem rep011 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_011.pointList FastDual33_011.columns FastDual33_011.rows FastDual33_011.bound (by decide +kernel)
    FastDual33_011.column_mask FastDual33_011.checked hc F hF hroot hmin hout

theorem query273 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {1,6,9,11} := rep011 halph

theorem rep012 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_012.pointList FastDual33_012.columns FastDual33_012.rows FastDual33_012.bound (by decide +kernel)
    FastDual33_012.column_mask FastDual33_012.checked hc F hF hroot hmin hout

theorem query274 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {1,6,10,11} := rep012 halph

theorem rep013 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_013.pointList FastDual33_013.columns FastDual33_013.rows FastDual33_013.bound (by decide +kernel)
    FastDual33_013.column_mask FastDual33_013.checked hc F hF hroot hmin hout

theorem query278 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {1,7,9,10} := rep013 halph

theorem rep014 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_014.pointList FastDual33_014.columns FastDual33_014.rows FastDual33_014.bound (by decide +kernel)
    FastDual33_014.column_mask FastDual33_014.checked hc F hF hroot hmin hout

theorem query279 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {1,7,9,11} := rep014 halph

theorem rep015 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_015.pointList FastDual33_015.columns FastDual33_015.rows FastDual33_015.bound (by decide +kernel)
    FastDual33_015.column_mask FastDual33_015.checked hc F hF hroot hmin hout

theorem query280 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {1,7,10,11} := rep015 halph

theorem rep016 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_016.pointList FastDual33_016.columns FastDual33_016.rows FastDual33_016.bound (by decide +kernel)
    FastDual33_016.column_mask FastDual33_016.checked hc F hF hroot hmin hout

theorem query406 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {3,6,7,9} := rep016 halph

theorem rep017 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_017.pointList FastDual33_017.columns FastDual33_017.rows FastDual33_017.bound (by decide +kernel)
    FastDual33_017.column_mask FastDual33_017.checked hc F hF hroot hmin hout

theorem query407 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {3,6,7,10} := rep017 halph

theorem rep018 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_018.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_018.pointList FastDual33_018.columns FastDual33_018.rows FastDual33_018.bound (by decide +kernel)
    FastDual33_018.column_mask FastDual33_018.checked hc F hF hroot hmin hout

theorem query408 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {3,6,7,11} := rep018 halph

theorem rep019 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_019.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_019.pointList FastDual33_019.columns FastDual33_019.rows FastDual33_019.bound (by decide +kernel)
    FastDual33_019.column_mask FastDual33_019.checked hc F hF hroot hmin hout

theorem query412 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {3,6,9,10} := rep019 halph

theorem rep020 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_020.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_020.pointList FastDual33_020.columns FastDual33_020.rows FastDual33_020.bound (by decide +kernel)
    FastDual33_020.column_mask FastDual33_020.checked hc F hF hroot hmin hout

theorem query413 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {3,6,9,11} := rep020 halph

theorem rep021 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_021.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_021.pointList FastDual33_021.columns FastDual33_021.rows FastDual33_021.bound (by decide +kernel)
    FastDual33_021.column_mask FastDual33_021.checked hc F hF hroot hmin hout

theorem query414 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {3,6,10,11} := rep021 halph

theorem rep022 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_022.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_022.pointList FastDual33_022.columns FastDual33_022.rows FastDual33_022.bound (by decide +kernel)
    FastDual33_022.column_mask FastDual33_022.checked hc F hF hroot hmin hout

theorem query418 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {3,7,9,10} := rep022 halph

theorem rep023 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_023.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_023.pointList FastDual33_023.columns FastDual33_023.rows FastDual33_023.bound (by decide +kernel)
    FastDual33_023.column_mask FastDual33_023.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {3,7,9,11} := rep023 halph

theorem rep024 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_024.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_024.pointList FastDual33_024.columns FastDual33_024.rows FastDual33_024.bound (by decide +kernel)
    FastDual33_024.column_mask FastDual33_024.checked hc F hF hroot hmin hout

theorem query420 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {3,7,10,11} := rep024 halph

theorem rep025 (halph : AlphabetComplete link33 alphabets) :
    ActualObstruction link33 FastDual33_025.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link33 rootCodes root_binding alphabets halph nonincident_complete
    FastDual33_025.pointList FastDual33_025.columns FastDual33_025.rows FastDual33_025.bound (by decide +kernel)
    FastDual33_025.column_mask FastDual33_025.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link33 alphabets) : ActualObstruction link33 {6,7,10,11} := rep025 halph

def dualQuads : List (Finset Point) := [{1,3,6,9},{1,3,6,10},{1,3,6,11},{1,3,7,9},{1,3,7,10},{1,3,7,11},{1,3,9,11},{1,6,7,9},{1,6,7,10},{1,6,7,11},{1,6,9,10},{1,6,9,11},{1,6,10,11},{1,7,9,10},{1,7,9,11},{1,7,10,11},{3,6,7,9},{3,6,7,10},{3,6,7,11},{3,6,9,10},{3,6,9,11},{3,6,10,11},{3,7,9,10},{3,7,9,11},{3,7,10,11},{6,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link33 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link33 Q := by
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

theorem all_foursets (halph : AlphabetComplete link33 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link33 Q :=
  class_census link33 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source33
