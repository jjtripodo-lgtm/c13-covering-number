import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source40
import C13Global.FastGroups.Source40Part00
import C13Global.FastGroups.Source40Part01
import C13Global.FastGroups.Source40Part02
import C13Global.FastGroups.Source40Part03
import C13Global.FastGroups.Source40Part04
import C13Global.FastGroups.Source40Part05
import C13Global.FastGroups.Source40Part06
namespace C13.Global.Relative.Source40
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source40
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link40 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link40 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link40 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link40 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_000.pointList FastDual40_000.columns FastDual40_000.rows FastDual40_000.bound (by decide +kernel)
    FastDual40_000.column_mask FastDual40_000.checked hc F hF hroot hmin hout

theorem query167 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,2,3,6} := rep000 halph

theorem rep001 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_001.pointList FastDual40_001.columns FastDual40_001.rows FastDual40_001.bound (by decide +kernel)
    FastDual40_001.column_mask FastDual40_001.checked hc F hF hroot hmin hout

theorem query169 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,2,3,8} := rep001 halph

theorem rep002 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_002.pointList FastDual40_002.columns FastDual40_002.rows FastDual40_002.bound (by decide +kernel)
    FastDual40_002.column_mask FastDual40_002.checked hc F hF hroot hmin hout

theorem query187 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,2,6,8} := rep002 halph

theorem rep003 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_003.pointList FastDual40_003.columns FastDual40_003.rows FastDual40_003.bound (by decide +kernel)
    FastDual40_003.column_mask FastDual40_003.checked hc F hF hroot hmin hout

theorem query188 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,2,6,9} := rep003 halph

theorem rep004 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_004.pointList FastDual40_004.columns FastDual40_004.rows FastDual40_004.bound (by decide +kernel)
    FastDual40_004.column_mask FastDual40_004.checked hc F hF hroot hmin hout

theorem query190 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,2,6,11} := rep004 halph

theorem rep005 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_005.pointList FastDual40_005.columns FastDual40_005.rows FastDual40_005.bound (by decide +kernel)
    FastDual40_005.column_mask FastDual40_005.checked hc F hF hroot hmin hout

theorem query191 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,2,7,8} := rep005 halph

theorem rep006 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_006.pointList FastDual40_006.columns FastDual40_006.rows FastDual40_006.bound (by decide +kernel)
    FastDual40_006.column_mask FastDual40_006.checked hc F hF hroot hmin hout

theorem query192 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,2,7,9} := rep006 halph

theorem rep007 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_007.pointList FastDual40_007.columns FastDual40_007.rows FastDual40_007.bound (by decide +kernel)
    FastDual40_007.column_mask FastDual40_007.checked hc F hF hroot hmin hout

theorem query194 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,2,7,11} := rep007 halph

theorem rep008 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_008.pointList FastDual40_008.columns FastDual40_008.rows FastDual40_008.bound (by decide +kernel)
    FastDual40_008.column_mask FastDual40_008.checked hc F hF hroot hmin hout

theorem query197 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,2,8,11} := rep008 halph

theorem rep009 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_009.pointList FastDual40_009.columns FastDual40_009.rows FastDual40_009.bound (by decide +kernel)
    FastDual40_009.column_mask FastDual40_009.checked hc F hF hroot hmin hout

theorem query215 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,3,6,8} := rep009 halph

theorem rep010 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_010.pointList FastDual40_010.columns FastDual40_010.rows FastDual40_010.bound (by decide +kernel)
    FastDual40_010.column_mask FastDual40_010.checked hc F hF hroot hmin hout

theorem query216 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,3,6,9} := rep010 halph

theorem rep011 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_011.pointList FastDual40_011.columns FastDual40_011.rows FastDual40_011.bound (by decide +kernel)
    FastDual40_011.column_mask FastDual40_011.checked hc F hF hroot hmin hout

theorem query218 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,3,6,11} := rep011 halph

theorem rep012 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_012.pointList FastDual40_012.columns FastDual40_012.rows FastDual40_012.bound (by decide +kernel)
    FastDual40_012.column_mask FastDual40_012.checked hc F hF hroot hmin hout

theorem query219 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,3,7,8} := rep012 halph

theorem rep013 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_013.pointList FastDual40_013.columns FastDual40_013.rows FastDual40_013.bound (by decide +kernel)
    FastDual40_013.column_mask FastDual40_013.checked hc F hF hroot hmin hout

theorem query220 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,3,7,9} := rep013 halph

theorem rep014 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_014.pointList FastDual40_014.columns FastDual40_014.rows FastDual40_014.bound (by decide +kernel)
    FastDual40_014.column_mask FastDual40_014.checked hc F hF hroot hmin hout

theorem query222 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,3,7,11} := rep014 halph

theorem rep015 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_015.pointList FastDual40_015.columns FastDual40_015.rows FastDual40_015.bound (by decide +kernel)
    FastDual40_015.column_mask FastDual40_015.checked hc F hF hroot hmin hout

theorem query227 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,3,9,11} := rep015 halph

theorem rep016 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_016.pointList FastDual40_016.columns FastDual40_016.rows FastDual40_016.bound (by decide +kernel)
    FastDual40_016.column_mask FastDual40_016.checked hc F hF hroot hmin hout

theorem query265 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,6,7,8} := rep016 halph

theorem rep017 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_017.pointList FastDual40_017.columns FastDual40_017.rows FastDual40_017.bound (by decide +kernel)
    FastDual40_017.column_mask FastDual40_017.checked hc F hF hroot hmin hout

theorem query266 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,6,7,9} := rep017 halph

theorem rep018 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_018.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_018.pointList FastDual40_018.columns FastDual40_018.rows FastDual40_018.bound (by decide +kernel)
    FastDual40_018.column_mask FastDual40_018.checked hc F hF hroot hmin hout

theorem query268 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,6,7,11} := rep018 halph

theorem rep019 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_019.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_019.pointList FastDual40_019.columns FastDual40_019.rows FastDual40_019.bound (by decide +kernel)
    FastDual40_019.column_mask FastDual40_019.checked hc F hF hroot hmin hout

theorem query269 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,6,8,9} := rep019 halph

theorem rep020 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_020.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_020.pointList FastDual40_020.columns FastDual40_020.rows FastDual40_020.bound (by decide +kernel)
    FastDual40_020.column_mask FastDual40_020.checked hc F hF hroot hmin hout

theorem query271 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,6,8,11} := rep020 halph

theorem rep021 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_021.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_021.pointList FastDual40_021.columns FastDual40_021.rows FastDual40_021.bound (by decide +kernel)
    FastDual40_021.column_mask FastDual40_021.checked hc F hF hroot hmin hout

theorem query273 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,6,9,11} := rep021 halph

theorem rep022 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_022.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_022.pointList FastDual40_022.columns FastDual40_022.rows FastDual40_022.bound (by decide +kernel)
    FastDual40_022.column_mask FastDual40_022.checked hc F hF hroot hmin hout

theorem query275 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,7,8,9} := rep022 halph

theorem rep023 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_023.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_023.pointList FastDual40_023.columns FastDual40_023.rows FastDual40_023.bound (by decide +kernel)
    FastDual40_023.column_mask FastDual40_023.checked hc F hF hroot hmin hout

theorem query277 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,7,8,11} := rep023 halph

theorem rep024 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_024.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_024.pointList FastDual40_024.columns FastDual40_024.rows FastDual40_024.bound (by decide +kernel)
    FastDual40_024.column_mask FastDual40_024.checked hc F hF hroot hmin hout

theorem query279 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {1,7,9,11} := rep024 halph

theorem rep025 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_025.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_025.pointList FastDual40_025.columns FastDual40_025.rows FastDual40_025.bound (by decide +kernel)
    FastDual40_025.column_mask FastDual40_025.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,3,6,7} := rep025 halph

theorem rep026 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_026.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_026.pointList FastDual40_026.columns FastDual40_026.rows FastDual40_026.bound (by decide +kernel)
    FastDual40_026.column_mask FastDual40_026.checked hc F hF hroot hmin hout

theorem query299 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,3,6,8} := rep026 halph

theorem rep027 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_027.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_027.pointList FastDual40_027.columns FastDual40_027.rows FastDual40_027.bound (by decide +kernel)
    FastDual40_027.column_mask FastDual40_027.checked hc F hF hroot hmin hout

theorem query300 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,3,6,9} := rep027 halph

theorem rep028 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_028.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_028.pointList FastDual40_028.columns FastDual40_028.rows FastDual40_028.bound (by decide +kernel)
    FastDual40_028.column_mask FastDual40_028.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,3,6,11} := rep028 halph

theorem rep029 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_029.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_029.pointList FastDual40_029.columns FastDual40_029.rows FastDual40_029.bound (by decide +kernel)
    FastDual40_029.column_mask FastDual40_029.checked hc F hF hroot hmin hout

theorem query303 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,3,7,8} := rep029 halph

theorem rep030 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_030.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_030.pointList FastDual40_030.columns FastDual40_030.rows FastDual40_030.bound (by decide +kernel)
    FastDual40_030.column_mask FastDual40_030.checked hc F hF hroot hmin hout

theorem query304 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,3,7,9} := rep030 halph

theorem rep031 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_031.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_031.pointList FastDual40_031.columns FastDual40_031.rows FastDual40_031.bound (by decide +kernel)
    FastDual40_031.column_mask FastDual40_031.checked hc F hF hroot hmin hout

theorem query306 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,3,7,11} := rep031 halph

theorem rep032 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_032.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_032.pointList FastDual40_032.columns FastDual40_032.rows FastDual40_032.bound (by decide +kernel)
    FastDual40_032.column_mask FastDual40_032.checked hc F hF hroot hmin hout

theorem query307 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,3,8,9} := rep032 halph

theorem rep033 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_033.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_033.pointList FastDual40_033.columns FastDual40_033.rows FastDual40_033.bound (by decide +kernel)
    FastDual40_033.column_mask FastDual40_033.checked hc F hF hroot hmin hout

theorem query349 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,6,7,8} := rep033 halph

theorem rep034 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_034.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_034.pointList FastDual40_034.columns FastDual40_034.rows FastDual40_034.bound (by decide +kernel)
    FastDual40_034.column_mask FastDual40_034.checked hc F hF hroot hmin hout

theorem query350 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,6,7,9} := rep034 halph

theorem rep035 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_035.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_035.pointList FastDual40_035.columns FastDual40_035.rows FastDual40_035.bound (by decide +kernel)
    FastDual40_035.column_mask FastDual40_035.checked hc F hF hroot hmin hout

theorem query352 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,6,7,11} := rep035 halph

theorem rep036 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_036.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_036.pointList FastDual40_036.columns FastDual40_036.rows FastDual40_036.bound (by decide +kernel)
    FastDual40_036.column_mask FastDual40_036.checked hc F hF hroot hmin hout

theorem query353 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,6,8,9} := rep036 halph

theorem rep037 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_037.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_037.pointList FastDual40_037.columns FastDual40_037.rows FastDual40_037.bound (by decide +kernel)
    FastDual40_037.column_mask FastDual40_037.checked hc F hF hroot hmin hout

theorem query355 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,6,8,11} := rep037 halph

theorem rep038 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_038.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_038.pointList FastDual40_038.columns FastDual40_038.rows FastDual40_038.bound (by decide +kernel)
    FastDual40_038.column_mask FastDual40_038.checked hc F hF hroot hmin hout

theorem query357 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,6,9,11} := rep038 halph

theorem rep039 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_039.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_039.pointList FastDual40_039.columns FastDual40_039.rows FastDual40_039.bound (by decide +kernel)
    FastDual40_039.column_mask FastDual40_039.checked hc F hF hroot hmin hout

theorem query359 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,7,8,9} := rep039 halph

theorem rep040 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_040.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_040.pointList FastDual40_040.columns FastDual40_040.rows FastDual40_040.bound (by decide +kernel)
    FastDual40_040.column_mask FastDual40_040.checked hc F hF hroot hmin hout

theorem query361 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,7,8,11} := rep040 halph

theorem rep041 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_041.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_041.pointList FastDual40_041.columns FastDual40_041.rows FastDual40_041.bound (by decide +kernel)
    FastDual40_041.column_mask FastDual40_041.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {2,7,9,11} := rep041 halph

theorem rep042 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_042.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_042.pointList FastDual40_042.columns FastDual40_042.rows FastDual40_042.bound (by decide +kernel)
    FastDual40_042.column_mask FastDual40_042.checked hc F hF hroot hmin hout

theorem query405 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {3,6,7,8} := rep042 halph

theorem rep043 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_043.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_043.pointList FastDual40_043.columns FastDual40_043.rows FastDual40_043.bound (by decide +kernel)
    FastDual40_043.column_mask FastDual40_043.checked hc F hF hroot hmin hout

theorem query406 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {3,6,7,9} := rep043 halph

theorem rep044 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_044.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_044.pointList FastDual40_044.columns FastDual40_044.rows FastDual40_044.bound (by decide +kernel)
    FastDual40_044.column_mask FastDual40_044.checked hc F hF hroot hmin hout

theorem query408 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {3,6,7,11} := rep044 halph

theorem rep045 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_045.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_045.pointList FastDual40_045.columns FastDual40_045.rows FastDual40_045.bound (by decide +kernel)
    FastDual40_045.column_mask FastDual40_045.checked hc F hF hroot hmin hout

theorem query409 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {3,6,8,9} := rep045 halph

theorem rep046 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_046.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_046.pointList FastDual40_046.columns FastDual40_046.rows FastDual40_046.bound (by decide +kernel)
    FastDual40_046.column_mask FastDual40_046.checked hc F hF hroot hmin hout

theorem query411 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {3,6,8,11} := rep046 halph

theorem rep047 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_047.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_047.pointList FastDual40_047.columns FastDual40_047.rows FastDual40_047.bound (by decide +kernel)
    FastDual40_047.column_mask FastDual40_047.checked hc F hF hroot hmin hout

theorem query413 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {3,6,9,11} := rep047 halph

theorem rep048 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_048.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_048.pointList FastDual40_048.columns FastDual40_048.rows FastDual40_048.bound (by decide +kernel)
    FastDual40_048.column_mask FastDual40_048.checked hc F hF hroot hmin hout

theorem query415 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {3,7,8,9} := rep048 halph

theorem rep049 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_049.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_049.pointList FastDual40_049.columns FastDual40_049.rows FastDual40_049.bound (by decide +kernel)
    FastDual40_049.column_mask FastDual40_049.checked hc F hF hroot hmin hout

theorem query417 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {3,7,8,11} := rep049 halph

theorem rep050 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_050.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_050.pointList FastDual40_050.columns FastDual40_050.rows FastDual40_050.bound (by decide +kernel)
    FastDual40_050.column_mask FastDual40_050.checked hc F hF hroot hmin hout

theorem query419 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {3,7,9,11} := rep050 halph

theorem rep051 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_051.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_051.pointList FastDual40_051.columns FastDual40_051.rows FastDual40_051.bound (by decide +kernel)
    FastDual40_051.column_mask FastDual40_051.checked hc F hF hroot hmin hout

theorem query480 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {6,7,8,9} := rep051 halph

theorem rep052 (halph : AlphabetComplete link40 alphabets) :
    ActualObstruction link40 FastDual40_052.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link40 rootCodes root_binding alphabets halph nonincident_complete
    FastDual40_052.pointList FastDual40_052.columns FastDual40_052.rows FastDual40_052.bound (by decide +kernel)
    FastDual40_052.column_mask FastDual40_052.checked hc F hF hroot hmin hout

theorem query487 (halph : AlphabetComplete link40 alphabets) : ActualObstruction link40 {6,8,9,11} := rep052 halph

def dualQuads : List (Finset Point) := [{1,2,3,6},{1,2,3,8},{1,2,6,8},{1,2,6,9},{1,2,6,11},{1,2,7,8},{1,2,7,9},{1,2,7,11},{1,2,8,11},{1,3,6,8},{1,3,6,9},{1,3,6,11},{1,3,7,8},{1,3,7,9},{1,3,7,11},{1,3,9,11},{1,6,7,8},{1,6,7,9},{1,6,7,11},{1,6,8,9},{1,6,8,11},{1,6,9,11},{1,7,8,9},{1,7,8,11},{1,7,9,11},{2,3,6,7},{2,3,6,8},{2,3,6,9},{2,3,6,11},{2,3,7,8},{2,3,7,9},{2,3,7,11},{2,3,8,9},{2,6,7,8},{2,6,7,9},{2,6,7,11},{2,6,8,9},{2,6,8,11},{2,6,9,11},{2,7,8,9},{2,7,8,11},{2,7,9,11},{3,6,7,8},{3,6,7,9},{3,6,7,11},{3,6,8,9},{3,6,8,11},{3,6,9,11},{3,7,8,9},{3,7,8,11},{3,7,9,11},{6,7,8,9},{6,8,9,11}]

theorem dual_actual (halph : AlphabetComplete link40 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link40 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query167 halph
  · exact query169 halph
  · exact query187 halph
  · exact query188 halph
  · exact query190 halph
  · exact query191 halph
  · exact query192 halph
  · exact query194 halph
  · exact query197 halph
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

theorem all_foursets (halph : AlphabetComplete link40 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link40 Q :=
  class_census link40 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source40
