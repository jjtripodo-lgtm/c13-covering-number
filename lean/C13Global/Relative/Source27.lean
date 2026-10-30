import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source27
import C13Global.FastGroups.Source27Part00
import C13Global.FastGroups.Source27Part01
import C13Global.FastGroups.Source27Part02
import C13Global.FastGroups.Source27Part03
namespace C13.Global.Relative.Source27
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source27
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link27 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link27 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link27 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link27 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_000.pointList FastDual27_000.columns FastDual27_000.rows FastDual27_000.bound (by decide +kernel)
    FastDual27_000.column_mask FastDual27_000.checked hc F hF hroot hmin hout

theorem query170 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,2,3,9} := rep000 halph

theorem rep001 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_001.pointList FastDual27_001.columns FastDual27_001.rows FastDual27_001.bound (by decide +kernel)
    FastDual27_001.column_mask FastDual27_001.checked hc F hF hroot hmin hout

theorem query188 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,2,6,9} := rep001 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link27 = link27 :=
  root_symmetry_of_codes rootCodes link27 root_binding automorphism000 (by decide +kernel)

theorem query220 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,3,7,9} :=
  obstruction_transport link27 FastDual27_001.points {1,3,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_002.pointList FastDual27_002.columns FastDual27_002.rows FastDual27_002.bound (by decide +kernel)
    FastDual27_002.column_mask FastDual27_002.checked hc F hF hroot hmin hout

theorem query189 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,2,6,10} := rep002 halph

theorem query222 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,3,7,11} :=
  obstruction_transport link27 FastDual27_002.points {1,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_003.pointList FastDual27_003.columns FastDual27_003.rows FastDual27_003.bound (by decide +kernel)
    FastDual27_003.column_mask FastDual27_003.checked hc F hF hroot hmin hout

theorem query190 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,2,6,11} := rep003 halph

theorem query221 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,3,7,10} :=
  obstruction_transport link27 FastDual27_003.points {1,3,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_004.pointList FastDual27_004.columns FastDual27_004.rows FastDual27_004.bound (by decide +kernel)
    FastDual27_004.column_mask FastDual27_004.checked hc F hF hroot hmin hout

theorem query192 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,2,7,9} := rep004 halph

theorem query216 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,3,6,9} :=
  obstruction_transport link27 FastDual27_004.points {1,3,6,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_005.pointList FastDual27_005.columns FastDual27_005.rows FastDual27_005.bound (by decide +kernel)
    FastDual27_005.column_mask FastDual27_005.checked hc F hF hroot hmin hout

theorem query193 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,2,7,10} := rep005 halph

theorem query218 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,3,6,11} :=
  obstruction_transport link27 FastDual27_005.points {1,3,6,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_006.pointList FastDual27_006.columns FastDual27_006.rows FastDual27_006.bound (by decide +kernel)
    FastDual27_006.column_mask FastDual27_006.checked hc F hF hroot hmin hout

theorem query194 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,2,7,11} := rep006 halph

theorem query217 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,3,6,10} :=
  obstruction_transport link27 FastDual27_006.points {1,3,6,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_007.pointList FastDual27_007.columns FastDual27_007.rows FastDual27_007.bound (by decide +kernel)
    FastDual27_007.column_mask FastDual27_007.checked hc F hF hroot hmin hout

theorem query198 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,2,9,10} := rep007 halph

theorem query227 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,3,9,11} :=
  obstruction_transport link27 FastDual27_007.points {1,3,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_008.pointList FastDual27_008.columns FastDual27_008.rows FastDual27_008.bound (by decide +kernel)
    FastDual27_008.column_mask FastDual27_008.checked hc F hF hroot hmin hout

theorem query266 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,6,7,9} := rep008 halph

theorem rep009 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_009.pointList FastDual27_009.columns FastDual27_009.rows FastDual27_009.bound (by decide +kernel)
    FastDual27_009.column_mask FastDual27_009.checked hc F hF hroot hmin hout

theorem query267 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,6,7,10} := rep009 halph

theorem query268 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,6,7,11} :=
  obstruction_transport link27 FastDual27_009.points {1,6,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_010.pointList FastDual27_010.columns FastDual27_010.rows FastDual27_010.bound (by decide +kernel)
    FastDual27_010.column_mask FastDual27_010.checked hc F hF hroot hmin hout

theorem query272 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,6,9,10} := rep010 halph

theorem query279 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,7,9,11} :=
  obstruction_transport link27 FastDual27_010.points {1,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_011.pointList FastDual27_011.columns FastDual27_011.rows FastDual27_011.bound (by decide +kernel)
    FastDual27_011.column_mask FastDual27_011.checked hc F hF hroot hmin hout

theorem query273 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,6,9,11} := rep011 halph

theorem query278 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,7,9,10} :=
  obstruction_transport link27 FastDual27_011.points {1,7,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_012.pointList FastDual27_012.columns FastDual27_012.rows FastDual27_012.bound (by decide +kernel)
    FastDual27_012.column_mask FastDual27_012.checked hc F hF hroot hmin hout

theorem query274 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,6,10,11} := rep012 halph

theorem query280 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {1,7,10,11} :=
  obstruction_transport link27 FastDual27_012.points {1,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep012 halph)

theorem rep013 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_013.pointList FastDual27_013.columns FastDual27_013.rows FastDual27_013.bound (by decide +kernel)
    FastDual27_013.column_mask FastDual27_013.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,3,6,7} := rep013 halph

theorem rep014 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_014.pointList FastDual27_014.columns FastDual27_014.rows FastDual27_014.bound (by decide +kernel)
    FastDual27_014.column_mask FastDual27_014.checked hc F hF hroot hmin hout

theorem query300 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,3,6,9} := rep014 halph

theorem query304 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,3,7,9} :=
  obstruction_transport link27 FastDual27_014.points {2,3,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep014 halph)

theorem rep015 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_015.pointList FastDual27_015.columns FastDual27_015.rows FastDual27_015.bound (by decide +kernel)
    FastDual27_015.column_mask FastDual27_015.checked hc F hF hroot hmin hout

theorem query301 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,3,6,10} := rep015 halph

theorem query306 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,3,7,11} :=
  obstruction_transport link27 FastDual27_015.points {2,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep015 halph)

theorem rep016 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_016.pointList FastDual27_016.columns FastDual27_016.rows FastDual27_016.bound (by decide +kernel)
    FastDual27_016.column_mask FastDual27_016.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,3,6,11} := rep016 halph

theorem query305 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,3,7,10} :=
  obstruction_transport link27 FastDual27_016.points {2,3,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep016 halph)

theorem rep017 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_017.pointList FastDual27_017.columns FastDual27_017.rows FastDual27_017.bound (by decide +kernel)
    FastDual27_017.column_mask FastDual27_017.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,3,10,11} := rep017 halph

theorem rep018 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_018.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_018.pointList FastDual27_018.columns FastDual27_018.rows FastDual27_018.bound (by decide +kernel)
    FastDual27_018.column_mask FastDual27_018.checked hc F hF hroot hmin hout

theorem query350 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,6,7,9} := rep018 halph

theorem query406 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {3,6,7,9} :=
  obstruction_transport link27 FastDual27_018.points {3,6,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep018 halph)

theorem rep019 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_019.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_019.pointList FastDual27_019.columns FastDual27_019.rows FastDual27_019.bound (by decide +kernel)
    FastDual27_019.column_mask FastDual27_019.checked hc F hF hroot hmin hout

theorem query351 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,6,7,10} := rep019 halph

theorem query408 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {3,6,7,11} :=
  obstruction_transport link27 FastDual27_019.points {3,6,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep019 halph)

theorem rep020 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_020.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_020.pointList FastDual27_020.columns FastDual27_020.rows FastDual27_020.bound (by decide +kernel)
    FastDual27_020.column_mask FastDual27_020.checked hc F hF hroot hmin hout

theorem query352 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,6,7,11} := rep020 halph

theorem query407 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {3,6,7,10} :=
  obstruction_transport link27 FastDual27_020.points {3,6,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep020 halph)

theorem rep021 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_021.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_021.pointList FastDual27_021.columns FastDual27_021.rows FastDual27_021.bound (by decide +kernel)
    FastDual27_021.column_mask FastDual27_021.checked hc F hF hroot hmin hout

theorem query356 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,6,9,10} := rep021 halph

theorem query419 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {3,7,9,11} :=
  obstruction_transport link27 FastDual27_021.points {3,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep021 halph)

theorem rep022 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_022.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_022.pointList FastDual27_022.columns FastDual27_022.rows FastDual27_022.bound (by decide +kernel)
    FastDual27_022.column_mask FastDual27_022.checked hc F hF hroot hmin hout

theorem query357 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,6,9,11} := rep022 halph

theorem query418 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {3,7,9,10} :=
  obstruction_transport link27 FastDual27_022.points {3,7,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep022 halph)

theorem rep023 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_023.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_023.pointList FastDual27_023.columns FastDual27_023.rows FastDual27_023.bound (by decide +kernel)
    FastDual27_023.column_mask FastDual27_023.checked hc F hF hroot hmin hout

theorem query358 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,6,10,11} := rep023 halph

theorem query420 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {3,7,10,11} :=
  obstruction_transport link27 FastDual27_023.points {3,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep023 halph)

theorem rep024 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_024.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_024.pointList FastDual27_024.columns FastDual27_024.rows FastDual27_024.bound (by decide +kernel)
    FastDual27_024.column_mask FastDual27_024.checked hc F hF hroot hmin hout

theorem query362 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,7,9,10} := rep024 halph

theorem query413 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {3,6,9,11} :=
  obstruction_transport link27 FastDual27_024.points {3,6,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep024 halph)

theorem rep025 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_025.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_025.pointList FastDual27_025.columns FastDual27_025.rows FastDual27_025.bound (by decide +kernel)
    FastDual27_025.column_mask FastDual27_025.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,7,9,11} := rep025 halph

theorem query412 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {3,6,9,10} :=
  obstruction_transport link27 FastDual27_025.points {3,6,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep025 halph)

theorem rep026 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_026.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_026.pointList FastDual27_026.columns FastDual27_026.rows FastDual27_026.bound (by decide +kernel)
    FastDual27_026.column_mask FastDual27_026.checked hc F hF hroot hmin hout

theorem query364 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {2,7,10,11} := rep026 halph

theorem query414 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {3,6,10,11} :=
  obstruction_transport link27 FastDual27_026.points {3,6,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep026 halph)

theorem rep027 (halph : AlphabetComplete link27 alphabets) :
    ActualObstruction link27 FastDual27_027.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link27 rootCodes root_binding alphabets halph nonincident_complete
    FastDual27_027.pointList FastDual27_027.columns FastDual27_027.rows FastDual27_027.bound (by decide +kernel)
    FastDual27_027.column_mask FastDual27_027.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link27 alphabets) : ActualObstruction link27 {6,7,10,11} := rep027 halph

def dualQuads : List (Finset Point) := [{1,2,3,9},{1,2,6,9},{1,3,7,9},{1,2,6,10},{1,3,7,11},{1,2,6,11},{1,3,7,10},{1,2,7,9},{1,3,6,9},{1,2,7,10},{1,3,6,11},{1,2,7,11},{1,3,6,10},{1,2,9,10},{1,3,9,11},{1,6,7,9},{1,6,7,10},{1,6,7,11},{1,6,9,10},{1,7,9,11},{1,6,9,11},{1,7,9,10},{1,6,10,11},{1,7,10,11},{2,3,6,7},{2,3,6,9},{2,3,7,9},{2,3,6,10},{2,3,7,11},{2,3,6,11},{2,3,7,10},{2,3,10,11},{2,6,7,9},{3,6,7,9},{2,6,7,10},{3,6,7,11},{2,6,7,11},{3,6,7,10},{2,6,9,10},{3,7,9,11},{2,6,9,11},{3,7,9,10},{2,6,10,11},{3,7,10,11},{2,7,9,10},{3,6,9,11},{2,7,9,11},{3,6,9,10},{2,7,10,11},{3,6,10,11},{6,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link27 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link27 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query170 halph
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

theorem all_foursets (halph : AlphabetComplete link27 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link27 Q :=
  class_census link27 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source27
