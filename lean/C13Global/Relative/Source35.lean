import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source35
import C13Global.FastGroups.Source35Part00
import C13Global.FastGroups.Source35Part01
namespace C13.Global.Relative.Source35
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source35
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link35 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link35 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link35 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link35 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link35 alphabets) :
    ActualObstruction link35 FastDual35_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link35 rootCodes root_binding alphabets halph nonincident_complete
    FastDual35_000.pointList FastDual35_000.columns FastDual35_000.rows FastDual35_000.bound (by decide +kernel)
    FastDual35_000.column_mask FastDual35_000.checked hc F hF hroot hmin hout

theorem query216 (halph : AlphabetComplete link35 alphabets) : ActualObstruction link35 {1,3,6,9} := rep000 halph

theorem rep001 (halph : AlphabetComplete link35 alphabets) :
    ActualObstruction link35 FastDual35_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link35 rootCodes root_binding alphabets halph nonincident_complete
    FastDual35_001.pointList FastDual35_001.columns FastDual35_001.rows FastDual35_001.bound (by decide +kernel)
    FastDual35_001.column_mask FastDual35_001.checked hc F hF hroot hmin hout

theorem query217 (halph : AlphabetComplete link35 alphabets) : ActualObstruction link35 {1,3,6,10} := rep001 halph

theorem rep002 (halph : AlphabetComplete link35 alphabets) :
    ActualObstruction link35 FastDual35_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link35 rootCodes root_binding alphabets halph nonincident_complete
    FastDual35_002.pointList FastDual35_002.columns FastDual35_002.rows FastDual35_002.bound (by decide +kernel)
    FastDual35_002.column_mask FastDual35_002.checked hc F hF hroot hmin hout

theorem query218 (halph : AlphabetComplete link35 alphabets) : ActualObstruction link35 {1,3,6,11} := rep002 halph

theorem rep003 (halph : AlphabetComplete link35 alphabets) :
    ActualObstruction link35 FastDual35_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link35 rootCodes root_binding alphabets halph nonincident_complete
    FastDual35_003.pointList FastDual35_003.columns FastDual35_003.rows FastDual35_003.bound (by decide +kernel)
    FastDual35_003.column_mask FastDual35_003.checked hc F hF hroot hmin hout

theorem query227 (halph : AlphabetComplete link35 alphabets) : ActualObstruction link35 {1,3,9,11} := rep003 halph

theorem rep004 (halph : AlphabetComplete link35 alphabets) :
    ActualObstruction link35 FastDual35_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link35 rootCodes root_binding alphabets halph nonincident_complete
    FastDual35_004.pointList FastDual35_004.columns FastDual35_004.rows FastDual35_004.bound (by decide +kernel)
    FastDual35_004.column_mask FastDual35_004.checked hc F hF hroot hmin hout

theorem query272 (halph : AlphabetComplete link35 alphabets) : ActualObstruction link35 {1,6,9,10} := rep004 halph

theorem rep005 (halph : AlphabetComplete link35 alphabets) :
    ActualObstruction link35 FastDual35_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link35 rootCodes root_binding alphabets halph nonincident_complete
    FastDual35_005.pointList FastDual35_005.columns FastDual35_005.rows FastDual35_005.bound (by decide +kernel)
    FastDual35_005.column_mask FastDual35_005.checked hc F hF hroot hmin hout

theorem query273 (halph : AlphabetComplete link35 alphabets) : ActualObstruction link35 {1,6,9,11} := rep005 halph

theorem rep006 (halph : AlphabetComplete link35 alphabets) :
    ActualObstruction link35 FastDual35_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link35 rootCodes root_binding alphabets halph nonincident_complete
    FastDual35_006.pointList FastDual35_006.columns FastDual35_006.rows FastDual35_006.bound (by decide +kernel)
    FastDual35_006.column_mask FastDual35_006.checked hc F hF hroot hmin hout

theorem query274 (halph : AlphabetComplete link35 alphabets) : ActualObstruction link35 {1,6,10,11} := rep006 halph

theorem rep007 (halph : AlphabetComplete link35 alphabets) :
    ActualObstruction link35 FastDual35_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link35 rootCodes root_binding alphabets halph nonincident_complete
    FastDual35_007.pointList FastDual35_007.columns FastDual35_007.rows FastDual35_007.bound (by decide +kernel)
    FastDual35_007.column_mask FastDual35_007.checked hc F hF hroot hmin hout

theorem query412 (halph : AlphabetComplete link35 alphabets) : ActualObstruction link35 {3,6,9,10} := rep007 halph

theorem rep008 (halph : AlphabetComplete link35 alphabets) :
    ActualObstruction link35 FastDual35_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link35 rootCodes root_binding alphabets halph nonincident_complete
    FastDual35_008.pointList FastDual35_008.columns FastDual35_008.rows FastDual35_008.bound (by decide +kernel)
    FastDual35_008.column_mask FastDual35_008.checked hc F hF hroot hmin hout

theorem query413 (halph : AlphabetComplete link35 alphabets) : ActualObstruction link35 {3,6,9,11} := rep008 halph

theorem rep009 (halph : AlphabetComplete link35 alphabets) :
    ActualObstruction link35 FastDual35_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link35 rootCodes root_binding alphabets halph nonincident_complete
    FastDual35_009.pointList FastDual35_009.columns FastDual35_009.rows FastDual35_009.bound (by decide +kernel)
    FastDual35_009.column_mask FastDual35_009.checked hc F hF hroot hmin hout

theorem query414 (halph : AlphabetComplete link35 alphabets) : ActualObstruction link35 {3,6,10,11} := rep009 halph

def dualQuads : List (Finset Point) := [{1,3,6,9},{1,3,6,10},{1,3,6,11},{1,3,9,11},{1,6,9,10},{1,6,9,11},{1,6,10,11},{3,6,9,10},{3,6,9,11},{3,6,10,11}]

theorem dual_actual (halph : AlphabetComplete link35 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link35 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query216 halph
  · exact query217 halph
  · exact query218 halph
  · exact query227 halph
  · exact query272 halph
  · exact query273 halph
  · exact query274 halph
  · exact query412 halph
  · exact query413 halph
  · exact query414 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link35 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link35 Q :=
  class_census link35 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source35
