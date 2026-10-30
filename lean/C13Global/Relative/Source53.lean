import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source53
import C13Global.FastGroups.Source53Part00
import C13Global.FastGroups.Source53Part01
import C13Global.FastGroups.Source53Part02
import C13Global.FastGroups.Source53Part03
namespace C13.Global.Relative.Source53
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source53
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link53 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link53 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link53 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link53 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_000.pointList FastDual53_000.columns FastDual53_000.rows FastDual53_000.bound (by decide +kernel)
    FastDual53_000.column_mask FastDual53_000.checked hc F hF hroot hmin hout

theorem query170 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,2,3,9} := rep000 halph

theorem rep001 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_001.pointList FastDual53_001.columns FastDual53_001.rows FastDual53_001.bound (by decide +kernel)
    FastDual53_001.column_mask FastDual53_001.checked hc F hF hroot hmin hout

theorem query188 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,2,6,9} := rep001 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link53 = link53 :=
  root_symmetry_of_codes rootCodes link53 root_binding automorphism000 (by decide +kernel)

theorem query220 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,3,7,9} :=
  obstruction_transport link53 FastDual53_001.points {1,3,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_002.pointList FastDual53_002.columns FastDual53_002.rows FastDual53_002.bound (by decide +kernel)
    FastDual53_002.column_mask FastDual53_002.checked hc F hF hroot hmin hout

theorem query189 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,2,6,10} := rep002 halph

theorem query222 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,3,7,11} :=
  obstruction_transport link53 FastDual53_002.points {1,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_003.pointList FastDual53_003.columns FastDual53_003.rows FastDual53_003.bound (by decide +kernel)
    FastDual53_003.column_mask FastDual53_003.checked hc F hF hroot hmin hout

theorem query190 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,2,6,11} := rep003 halph

theorem query221 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,3,7,10} :=
  obstruction_transport link53 FastDual53_003.points {1,3,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_004.pointList FastDual53_004.columns FastDual53_004.rows FastDual53_004.bound (by decide +kernel)
    FastDual53_004.column_mask FastDual53_004.checked hc F hF hroot hmin hout

theorem query192 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,2,7,9} := rep004 halph

theorem query216 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,3,6,9} :=
  obstruction_transport link53 FastDual53_004.points {1,3,6,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_005.pointList FastDual53_005.columns FastDual53_005.rows FastDual53_005.bound (by decide +kernel)
    FastDual53_005.column_mask FastDual53_005.checked hc F hF hroot hmin hout

theorem query193 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,2,7,10} := rep005 halph

theorem query218 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,3,6,11} :=
  obstruction_transport link53 FastDual53_005.points {1,3,6,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_006.pointList FastDual53_006.columns FastDual53_006.rows FastDual53_006.bound (by decide +kernel)
    FastDual53_006.column_mask FastDual53_006.checked hc F hF hroot hmin hout

theorem query194 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,2,7,11} := rep006 halph

theorem query217 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,3,6,10} :=
  obstruction_transport link53 FastDual53_006.points {1,3,6,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_007.pointList FastDual53_007.columns FastDual53_007.rows FastDual53_007.bound (by decide +kernel)
    FastDual53_007.column_mask FastDual53_007.checked hc F hF hroot hmin hout

theorem query198 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,2,9,10} := rep007 halph

theorem query227 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,3,9,11} :=
  obstruction_transport link53 FastDual53_007.points {1,3,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_008.pointList FastDual53_008.columns FastDual53_008.rows FastDual53_008.bound (by decide +kernel)
    FastDual53_008.column_mask FastDual53_008.checked hc F hF hroot hmin hout

theorem query266 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,6,7,9} := rep008 halph

theorem rep009 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_009.pointList FastDual53_009.columns FastDual53_009.rows FastDual53_009.bound (by decide +kernel)
    FastDual53_009.column_mask FastDual53_009.checked hc F hF hroot hmin hout

theorem query267 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,6,7,10} := rep009 halph

theorem query268 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,6,7,11} :=
  obstruction_transport link53 FastDual53_009.points {1,6,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_010.pointList FastDual53_010.columns FastDual53_010.rows FastDual53_010.bound (by decide +kernel)
    FastDual53_010.column_mask FastDual53_010.checked hc F hF hroot hmin hout

theorem query272 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,6,9,10} := rep010 halph

theorem query279 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,7,9,11} :=
  obstruction_transport link53 FastDual53_010.points {1,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_011.pointList FastDual53_011.columns FastDual53_011.rows FastDual53_011.bound (by decide +kernel)
    FastDual53_011.column_mask FastDual53_011.checked hc F hF hroot hmin hout

theorem query273 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,6,9,11} := rep011 halph

theorem query278 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,7,9,10} :=
  obstruction_transport link53 FastDual53_011.points {1,7,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_012.pointList FastDual53_012.columns FastDual53_012.rows FastDual53_012.bound (by decide +kernel)
    FastDual53_012.column_mask FastDual53_012.checked hc F hF hroot hmin hout

theorem query274 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,6,10,11} := rep012 halph

theorem query280 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {1,7,10,11} :=
  obstruction_transport link53 FastDual53_012.points {1,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep012 halph)

theorem rep013 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_013.pointList FastDual53_013.columns FastDual53_013.rows FastDual53_013.bound (by decide +kernel)
    FastDual53_013.column_mask FastDual53_013.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,3,6,7} := rep013 halph

theorem rep014 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_014.pointList FastDual53_014.columns FastDual53_014.rows FastDual53_014.bound (by decide +kernel)
    FastDual53_014.column_mask FastDual53_014.checked hc F hF hroot hmin hout

theorem query300 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,3,6,9} := rep014 halph

theorem query304 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,3,7,9} :=
  obstruction_transport link53 FastDual53_014.points {2,3,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep014 halph)

theorem rep015 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_015.pointList FastDual53_015.columns FastDual53_015.rows FastDual53_015.bound (by decide +kernel)
    FastDual53_015.column_mask FastDual53_015.checked hc F hF hroot hmin hout

theorem query301 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,3,6,10} := rep015 halph

theorem query306 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,3,7,11} :=
  obstruction_transport link53 FastDual53_015.points {2,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep015 halph)

theorem rep016 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_016.pointList FastDual53_016.columns FastDual53_016.rows FastDual53_016.bound (by decide +kernel)
    FastDual53_016.column_mask FastDual53_016.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,3,6,11} := rep016 halph

theorem query305 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,3,7,10} :=
  obstruction_transport link53 FastDual53_016.points {2,3,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep016 halph)

theorem rep017 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_017.pointList FastDual53_017.columns FastDual53_017.rows FastDual53_017.bound (by decide +kernel)
    FastDual53_017.column_mask FastDual53_017.checked hc F hF hroot hmin hout

theorem query312 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,3,10,11} := rep017 halph

theorem rep018 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_018.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_018.pointList FastDual53_018.columns FastDual53_018.rows FastDual53_018.bound (by decide +kernel)
    FastDual53_018.column_mask FastDual53_018.checked hc F hF hroot hmin hout

theorem query350 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,6,7,9} := rep018 halph

theorem query406 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {3,6,7,9} :=
  obstruction_transport link53 FastDual53_018.points {3,6,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep018 halph)

theorem rep019 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_019.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_019.pointList FastDual53_019.columns FastDual53_019.rows FastDual53_019.bound (by decide +kernel)
    FastDual53_019.column_mask FastDual53_019.checked hc F hF hroot hmin hout

theorem query351 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,6,7,10} := rep019 halph

theorem query408 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {3,6,7,11} :=
  obstruction_transport link53 FastDual53_019.points {3,6,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep019 halph)

theorem rep020 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_020.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_020.pointList FastDual53_020.columns FastDual53_020.rows FastDual53_020.bound (by decide +kernel)
    FastDual53_020.column_mask FastDual53_020.checked hc F hF hroot hmin hout

theorem query352 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,6,7,11} := rep020 halph

theorem query407 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {3,6,7,10} :=
  obstruction_transport link53 FastDual53_020.points {3,6,7,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep020 halph)

theorem rep021 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_021.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_021.pointList FastDual53_021.columns FastDual53_021.rows FastDual53_021.bound (by decide +kernel)
    FastDual53_021.column_mask FastDual53_021.checked hc F hF hroot hmin hout

theorem query356 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,6,9,10} := rep021 halph

theorem query419 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {3,7,9,11} :=
  obstruction_transport link53 FastDual53_021.points {3,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep021 halph)

theorem rep022 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_022.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_022.pointList FastDual53_022.columns FastDual53_022.rows FastDual53_022.bound (by decide +kernel)
    FastDual53_022.column_mask FastDual53_022.checked hc F hF hroot hmin hout

theorem query357 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,6,9,11} := rep022 halph

theorem query418 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {3,7,9,10} :=
  obstruction_transport link53 FastDual53_022.points {3,7,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep022 halph)

theorem rep023 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_023.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_023.pointList FastDual53_023.columns FastDual53_023.rows FastDual53_023.bound (by decide +kernel)
    FastDual53_023.column_mask FastDual53_023.checked hc F hF hroot hmin hout

theorem query358 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,6,10,11} := rep023 halph

theorem query420 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {3,7,10,11} :=
  obstruction_transport link53 FastDual53_023.points {3,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep023 halph)

theorem rep024 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_024.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_024.pointList FastDual53_024.columns FastDual53_024.rows FastDual53_024.bound (by decide +kernel)
    FastDual53_024.column_mask FastDual53_024.checked hc F hF hroot hmin hout

theorem query362 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,7,9,10} := rep024 halph

theorem query413 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {3,6,9,11} :=
  obstruction_transport link53 FastDual53_024.points {3,6,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep024 halph)

theorem rep025 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_025.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_025.pointList FastDual53_025.columns FastDual53_025.rows FastDual53_025.bound (by decide +kernel)
    FastDual53_025.column_mask FastDual53_025.checked hc F hF hroot hmin hout

theorem query363 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,7,9,11} := rep025 halph

theorem query412 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {3,6,9,10} :=
  obstruction_transport link53 FastDual53_025.points {3,6,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep025 halph)

theorem rep026 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_026.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_026.pointList FastDual53_026.columns FastDual53_026.rows FastDual53_026.bound (by decide +kernel)
    FastDual53_026.column_mask FastDual53_026.checked hc F hF hroot hmin hout

theorem query364 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {2,7,10,11} := rep026 halph

theorem query414 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {3,6,10,11} :=
  obstruction_transport link53 FastDual53_026.points {3,6,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep026 halph)

theorem rep027 (halph : AlphabetComplete link53 alphabets) :
    ActualObstruction link53 FastDual53_027.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link53 rootCodes root_binding alphabets halph nonincident_complete
    FastDual53_027.pointList FastDual53_027.columns FastDual53_027.rows FastDual53_027.bound (by decide +kernel)
    FastDual53_027.column_mask FastDual53_027.checked hc F hF hroot hmin hout

theorem query485 (halph : AlphabetComplete link53 alphabets) : ActualObstruction link53 {6,7,10,11} := rep027 halph

def dualQuads : List (Finset Point) := [{1,2,3,9},{1,2,6,9},{1,3,7,9},{1,2,6,10},{1,3,7,11},{1,2,6,11},{1,3,7,10},{1,2,7,9},{1,3,6,9},{1,2,7,10},{1,3,6,11},{1,2,7,11},{1,3,6,10},{1,2,9,10},{1,3,9,11},{1,6,7,9},{1,6,7,10},{1,6,7,11},{1,6,9,10},{1,7,9,11},{1,6,9,11},{1,7,9,10},{1,6,10,11},{1,7,10,11},{2,3,6,7},{2,3,6,9},{2,3,7,9},{2,3,6,10},{2,3,7,11},{2,3,6,11},{2,3,7,10},{2,3,10,11},{2,6,7,9},{3,6,7,9},{2,6,7,10},{3,6,7,11},{2,6,7,11},{3,6,7,10},{2,6,9,10},{3,7,9,11},{2,6,9,11},{3,7,9,10},{2,6,10,11},{3,7,10,11},{2,7,9,10},{3,6,9,11},{2,7,9,11},{3,6,9,10},{2,7,10,11},{3,6,10,11},{6,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link53 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link53 Q := by
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

theorem all_foursets (halph : AlphabetComplete link53 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link53 Q :=
  class_census link53 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source53
