import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source26
import C13Global.FastGroups.Source26Part00
import C13Global.FastGroups.Source26Part01
import C13Global.FastGroups.Source26Part02
import C13Global.FastGroups.Source26Part03
namespace C13.Global.Relative.Source26
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source26
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link26 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link26 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link26 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link26 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_000.pointList FastDual26_000.columns FastDual26_000.rows FastDual26_000.bound (by decide +kernel)
    FastDual26_000.column_mask FastDual26_000.checked hc F hF hroot hmin hout

theorem query188 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,2,6,9} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link26 = link26 :=
  root_symmetry_of_codes rootCodes link26 root_binding automorphism000 (by decide +kernel)

theorem query220 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,3,7,9} :=
  obstruction_transport link26 FastDual26_000.points {1,3,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_001.pointList FastDual26_001.columns FastDual26_001.rows FastDual26_001.bound (by decide +kernel)
    FastDual26_001.column_mask FastDual26_001.checked hc F hF hroot hmin hout

theorem query189 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,2,6,10} := rep001 halph

theorem query222 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,3,7,11} :=
  obstruction_transport link26 FastDual26_001.points {1,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_002.pointList FastDual26_002.columns FastDual26_002.rows FastDual26_002.bound (by decide +kernel)
    FastDual26_002.column_mask FastDual26_002.checked hc F hF hroot hmin hout

theorem query190 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,2,6,11} := rep002 halph

theorem query221 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,3,7,10} :=
  obstruction_transport link26 FastDual26_002.points {1,3,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_003.pointList FastDual26_003.columns FastDual26_003.rows FastDual26_003.bound (by decide +kernel)
    FastDual26_003.column_mask FastDual26_003.checked hc F hF hroot hmin hout

theorem query192 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,2,7,9} := rep003 halph

theorem query216 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,3,6,9} :=
  obstruction_transport link26 FastDual26_003.points {1,3,6,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_004.pointList FastDual26_004.columns FastDual26_004.rows FastDual26_004.bound (by decide +kernel)
    FastDual26_004.column_mask FastDual26_004.checked hc F hF hroot hmin hout

theorem query193 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,2,7,10} := rep004 halph

theorem query218 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,3,6,11} :=
  obstruction_transport link26 FastDual26_004.points {1,3,6,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_005.pointList FastDual26_005.columns FastDual26_005.rows FastDual26_005.bound (by decide +kernel)
    FastDual26_005.column_mask FastDual26_005.checked hc F hF hroot hmin hout

theorem query194 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,2,7,11} := rep005 halph

theorem query217 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,3,6,10} :=
  obstruction_transport link26 FastDual26_005.points {1,3,6,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_006.pointList FastDual26_006.columns FastDual26_006.rows FastDual26_006.bound (by decide +kernel)
    FastDual26_006.column_mask FastDual26_006.checked hc F hF hroot hmin hout

theorem query198 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,2,9,10} := rep006 halph

theorem query227 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,3,9,11} :=
  obstruction_transport link26 FastDual26_006.points {1,3,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_007.pointList FastDual26_007.columns FastDual26_007.rows FastDual26_007.bound (by decide +kernel)
    FastDual26_007.column_mask FastDual26_007.checked hc F hF hroot hmin hout

theorem query266 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,6,7,9} := rep007 halph

theorem rep008 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_008.pointList FastDual26_008.columns FastDual26_008.rows FastDual26_008.bound (by decide +kernel)
    FastDual26_008.column_mask FastDual26_008.checked hc F hF hroot hmin hout

theorem query267 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,6,7,10} := rep008 halph

theorem query268 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,6,7,11} :=
  obstruction_transport link26 FastDual26_008.points {1,6,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_009.pointList FastDual26_009.columns FastDual26_009.rows FastDual26_009.bound (by decide +kernel)
    FastDual26_009.column_mask FastDual26_009.checked hc F hF hroot hmin hout

theorem query272 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,6,9,10} := rep009 halph

theorem query279 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,7,9,11} :=
  obstruction_transport link26 FastDual26_009.points {1,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_010.pointList FastDual26_010.columns FastDual26_010.rows FastDual26_010.bound (by decide +kernel)
    FastDual26_010.column_mask FastDual26_010.checked hc F hF hroot hmin hout

theorem query273 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,6,9,11} := rep010 halph

theorem query278 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,7,9,10} :=
  obstruction_transport link26 FastDual26_010.points {1,7,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_011.pointList FastDual26_011.columns FastDual26_011.rows FastDual26_011.bound (by decide +kernel)
    FastDual26_011.column_mask FastDual26_011.checked hc F hF hroot hmin hout

theorem query274 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,6,10,11} := rep011 halph

theorem query280 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {1,7,10,11} :=
  obstruction_transport link26 FastDual26_011.points {1,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_012.pointList FastDual26_012.columns FastDual26_012.rows FastDual26_012.bound (by decide +kernel)
    FastDual26_012.column_mask FastDual26_012.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,3,6,7} := rep012 halph

theorem rep013 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_013.pointList FastDual26_013.columns FastDual26_013.rows FastDual26_013.bound (by decide +kernel)
    FastDual26_013.column_mask FastDual26_013.checked hc F hF hroot hmin hout

theorem query300 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,3,6,9} := rep013 halph

theorem query304 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,3,7,9} :=
  obstruction_transport link26 FastDual26_013.points {2,3,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep013 halph)

theorem rep014 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_014.pointList FastDual26_014.columns FastDual26_014.rows FastDual26_014.bound (by decide +kernel)
    FastDual26_014.column_mask FastDual26_014.checked hc F hF hroot hmin hout

theorem query301 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,3,6,10} := rep014 halph

theorem query306 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,3,7,11} :=
  obstruction_transport link26 FastDual26_014.points {2,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep014 halph)

theorem rep015 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_015.pointList FastDual26_015.columns FastDual26_015.rows FastDual26_015.bound (by decide +kernel)
    FastDual26_015.column_mask FastDual26_015.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,3,6,11} := rep015 halph

theorem query305 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,3,7,10} :=
  obstruction_transport link26 FastDual26_015.points {2,3,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep015 halph)

theorem rep016 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_016.pointList FastDual26_016.columns FastDual26_016.rows FastDual26_016.bound (by decide +kernel)
    FastDual26_016.column_mask FastDual26_016.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,3,10,11} := rep016 halph

theorem rep017 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_017.pointList FastDual26_017.columns FastDual26_017.rows FastDual26_017.bound (by decide +kernel)
    FastDual26_017.column_mask FastDual26_017.checked hc F hF hroot hmin hout

theorem query350 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,6,7,9} := rep017 halph

theorem query406 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {3,6,7,9} :=
  obstruction_transport link26 FastDual26_017.points {3,6,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep017 halph)

theorem rep018 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_018.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_018.pointList FastDual26_018.columns FastDual26_018.rows FastDual26_018.bound (by decide +kernel)
    FastDual26_018.column_mask FastDual26_018.checked hc F hF hroot hmin hout

theorem query351 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,6,7,10} := rep018 halph

theorem query408 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {3,6,7,11} :=
  obstruction_transport link26 FastDual26_018.points {3,6,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep018 halph)

theorem rep019 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_019.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_019.pointList FastDual26_019.columns FastDual26_019.rows FastDual26_019.bound (by decide +kernel)
    FastDual26_019.column_mask FastDual26_019.checked hc F hF hroot hmin hout

theorem query352 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,6,7,11} := rep019 halph

theorem query407 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {3,6,7,10} :=
  obstruction_transport link26 FastDual26_019.points {3,6,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep019 halph)

theorem rep020 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_020.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_020.pointList FastDual26_020.columns FastDual26_020.rows FastDual26_020.bound (by decide +kernel)
    FastDual26_020.column_mask FastDual26_020.checked hc F hF hroot hmin hout

theorem query356 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,6,9,10} := rep020 halph

theorem query419 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {3,7,9,11} :=
  obstruction_transport link26 FastDual26_020.points {3,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep020 halph)

theorem rep021 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_021.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_021.pointList FastDual26_021.columns FastDual26_021.rows FastDual26_021.bound (by decide +kernel)
    FastDual26_021.column_mask FastDual26_021.checked hc F hF hroot hmin hout

theorem query357 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,6,9,11} := rep021 halph

theorem query418 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {3,7,9,10} :=
  obstruction_transport link26 FastDual26_021.points {3,7,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep021 halph)

theorem rep022 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_022.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_022.pointList FastDual26_022.columns FastDual26_022.rows FastDual26_022.bound (by decide +kernel)
    FastDual26_022.column_mask FastDual26_022.checked hc F hF hroot hmin hout

theorem query358 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,6,10,11} := rep022 halph

theorem query420 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {3,7,10,11} :=
  obstruction_transport link26 FastDual26_022.points {3,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep022 halph)

theorem rep023 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_023.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_023.pointList FastDual26_023.columns FastDual26_023.rows FastDual26_023.bound (by decide +kernel)
    FastDual26_023.column_mask FastDual26_023.checked hc F hF hroot hmin hout

theorem query362 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,7,9,10} := rep023 halph

theorem query413 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {3,6,9,11} :=
  obstruction_transport link26 FastDual26_023.points {3,6,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep023 halph)

theorem rep024 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_024.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_024.pointList FastDual26_024.columns FastDual26_024.rows FastDual26_024.bound (by decide +kernel)
    FastDual26_024.column_mask FastDual26_024.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,7,9,11} := rep024 halph

theorem query412 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {3,6,9,10} :=
  obstruction_transport link26 FastDual26_024.points {3,6,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep024 halph)

theorem rep025 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_025.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_025.pointList FastDual26_025.columns FastDual26_025.rows FastDual26_025.bound (by decide +kernel)
    FastDual26_025.column_mask FastDual26_025.checked hc F hF hroot hmin hout

theorem query364 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {2,7,10,11} := rep025 halph

theorem query414 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {3,6,10,11} :=
  obstruction_transport link26 FastDual26_025.points {3,6,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep025 halph)

theorem rep026 (halph : AlphabetComplete link26 alphabets) :
    ActualObstruction link26 FastDual26_026.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link26 rootCodes root_binding alphabets halph nonincident_complete
    FastDual26_026.pointList FastDual26_026.columns FastDual26_026.rows FastDual26_026.bound (by decide +kernel)
    FastDual26_026.column_mask FastDual26_026.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link26 alphabets) : ActualObstruction link26 {6,7,10,11} := rep026 halph

def dualQuads : List (Finset Point) := [{1,2,6,9},{1,3,7,9},{1,2,6,10},{1,3,7,11},{1,2,6,11},{1,3,7,10},{1,2,7,9},{1,3,6,9},{1,2,7,10},{1,3,6,11},{1,2,7,11},{1,3,6,10},{1,2,9,10},{1,3,9,11},{1,6,7,9},{1,6,7,10},{1,6,7,11},{1,6,9,10},{1,7,9,11},{1,6,9,11},{1,7,9,10},{1,6,10,11},{1,7,10,11},{2,3,6,7},{2,3,6,9},{2,3,7,9},{2,3,6,10},{2,3,7,11},{2,3,6,11},{2,3,7,10},{2,3,10,11},{2,6,7,9},{3,6,7,9},{2,6,7,10},{3,6,7,11},{2,6,7,11},{3,6,7,10},{2,6,9,10},{3,7,9,11},{2,6,9,11},{3,7,9,10},{2,6,10,11},{3,7,10,11},{2,7,9,10},{3,6,9,11},{2,7,9,11},{3,6,9,10},{2,7,10,11},{3,6,10,11},{6,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link26 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link26 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query188 halph
  · exact query220 halph
  · exact query189 halph
  · exact query222 halph
  · exact query190 halph
  · exact query221 halph
  · exact query192 halph
  · exact query216 halph
  · exact query193 halph
  · exact query218 halph
  · exact query194 halph
  · exact query217 halph
  · exact query198 halph
  · exact query227 halph
  · exact query266 halph
  · exact query267 halph
  · exact query268 halph
  · exact query272 halph
  · exact query279 halph
  · exact query273 halph
  · exact query278 halph
  · exact query274 halph
  · exact query280 halph
  · exact query298 halph
  · exact query300 halph
  · exact query304 halph
  · exact query301 halph
  · exact query306 halph
  · exact query302 halph
  · exact query305 halph
  · exact query312 halph
  · exact query350 halph
  · exact query406 halph
  · exact query351 halph
  · exact query408 halph
  · exact query352 halph
  · exact query407 halph
  · exact query356 halph
  · exact query419 halph
  · exact query357 halph
  · exact query418 halph
  · exact query358 halph
  · exact query420 halph
  · exact query362 halph
  · exact query413 halph
  · exact query363 halph
  · exact query412 halph
  · exact query364 halph
  · exact query414 halph
  · exact query485 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link26 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link26 Q :=
  class_census link26 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source26
