import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source64
import C13Global.FastGroups.Source64Part00
import C13Global.FastGroups.Source64Part01
import C13Global.FastGroups.Source64Part02
import C13Global.FastGroups.Source64Part03
namespace C13.Global.Relative.Source64
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source64
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link64 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link64 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link64 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link64 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_000.pointList FastDual64_000.columns FastDual64_000.rows FastDual64_000.bound (by decide +kernel)
    FastDual64_000.column_mask FastDual64_000.checked hc F hF hroot hmin hout

theorem query046 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,2,3,5} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![11,8,9,10,6,5,4,7,1,2,3,0,12]
  invFun := ![11,8,9,10,6,5,4,7,1,2,3,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link64 = link64 :=
  root_symmetry_of_codes rootCodes link64 root_binding automorphism000 (by decide +kernel)

theorem query479 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {5,9,10,11} :=
  obstruction_transport link64 FastDual64_000.points {5,9,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_001.pointList FastDual64_001.columns FastDual64_001.rows FastDual64_001.bound (by decide +kernel)
    FastDual64_001.column_mask FastDual64_001.checked hc F hF hroot hmin hout

theorem query052 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,2,3,11} := rep001 halph

theorem query164 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,9,10,11} :=
  obstruction_transport link64 FastDual64_001.points {0,9,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_002.pointList FastDual64_002.columns FastDual64_002.rows FastDual64_002.bound (by decide +kernel)
    FastDual64_002.column_mask FastDual64_002.checked hc F hF hroot hmin hout

theorem query061 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,2,5,7} := rep002 halph

theorem query474 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {5,7,9,11} :=
  obstruction_transport link64 FastDual64_002.points {5,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_003.pointList FastDual64_003.columns FastDual64_003.rows FastDual64_003.bound (by decide +kernel)
    FastDual64_003.column_mask FastDual64_003.checked hc F hF hroot hmin hout

theorem query063 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,2,5,9} := rep003 halph

theorem query347 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {2,5,9,11} :=
  obstruction_transport link64 FastDual64_003.points {2,5,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_004.pointList FastDual64_004.columns FastDual64_004.rows FastDual64_004.bound (by decide +kernel)
    FastDual64_004.column_mask FastDual64_004.checked hc F hF hroot hmin hout

theorem query064 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,2,5,10} := rep004 halph

theorem query403 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {3,5,9,11} :=
  obstruction_transport link64 FastDual64_004.points {3,5,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_005.pointList FastDual64_005.columns FastDual64_005.rows FastDual64_005.bound (by decide +kernel)
    FastDual64_005.column_mask FastDual64_005.checked hc F hF hroot hmin hout

theorem query065 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,2,5,11} := rep005 halph

theorem query143 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,5,9,11} :=
  obstruction_transport link64 FastDual64_005.points {0,5,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_006.pointList FastDual64_006.columns FastDual64_006.rows FastDual64_006.bound (by decide +kernel)
    FastDual64_006.column_mask FastDual64_006.checked hc F hF hroot hmin hout

theorem query072 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,2,7,9} := rep006 halph

theorem query363 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {2,7,9,11} :=
  obstruction_transport link64 FastDual64_006.points {2,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_007.pointList FastDual64_007.columns FastDual64_007.rows FastDual64_007.bound (by decide +kernel)
    FastDual64_007.column_mask FastDual64_007.checked hc F hF hroot hmin hout

theorem query073 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,2,7,10} := rep007 halph

theorem query419 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {3,7,9,11} :=
  obstruction_transport link64 FastDual64_007.points {3,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_008.pointList FastDual64_008.columns FastDual64_008.rows FastDual64_008.bound (by decide +kernel)
    FastDual64_008.column_mask FastDual64_008.checked hc F hF hroot hmin hout

theorem query074 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,2,7,11} := rep008 halph

theorem query159 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,7,9,11} :=
  obstruction_transport link64 FastDual64_008.points {0,7,9,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_009.pointList FastDual64_009.columns FastDual64_009.rows FastDual64_009.bound (by decide +kernel)
    FastDual64_009.column_mask FastDual64_009.checked hc F hF hroot hmin hout

theorem query079 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,2,9,11} := rep009 halph

theorem rep010 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_010.pointList FastDual64_010.columns FastDual64_010.rows FastDual64_010.bound (by decide +kernel)
    FastDual64_010.column_mask FastDual64_010.checked hc F hF hroot hmin hout

theorem query091 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,3,5,9} := rep010 halph

theorem query348 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {2,5,10,11} :=
  obstruction_transport link64 FastDual64_010.points {2,5,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_011.pointList FastDual64_011.columns FastDual64_011.rows FastDual64_011.bound (by decide +kernel)
    FastDual64_011.column_mask FastDual64_011.checked hc F hF hroot hmin hout

theorem query092 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,3,5,10} := rep011 halph

theorem query404 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {3,5,10,11} :=
  obstruction_transport link64 FastDual64_011.points {3,5,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_012.pointList FastDual64_012.columns FastDual64_012.rows FastDual64_012.bound (by decide +kernel)
    FastDual64_012.column_mask FastDual64_012.checked hc F hF hroot hmin hout

theorem query093 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,3,5,11} := rep012 halph

theorem query144 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,5,10,11} :=
  obstruction_transport link64 FastDual64_012.points {0,5,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep012 halph)

theorem rep013 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_013.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_013.pointList FastDual64_013.columns FastDual64_013.rows FastDual64_013.bound (by decide +kernel)
    FastDual64_013.column_mask FastDual64_013.checked hc F hF hroot hmin hout

theorem query100 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,3,7,9} := rep013 halph

theorem query364 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {2,7,10,11} :=
  obstruction_transport link64 FastDual64_013.points {2,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep013 halph)

theorem rep014 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_014.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_014.pointList FastDual64_014.columns FastDual64_014.rows FastDual64_014.bound (by decide +kernel)
    FastDual64_014.column_mask FastDual64_014.checked hc F hF hroot hmin hout

theorem query101 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,3,7,10} := rep014 halph

theorem query420 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {3,7,10,11} :=
  obstruction_transport link64 FastDual64_014.points {3,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep014 halph)

theorem rep015 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_015.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_015.pointList FastDual64_015.columns FastDual64_015.rows FastDual64_015.bound (by decide +kernel)
    FastDual64_015.column_mask FastDual64_015.checked hc F hF hroot hmin hout

theorem query102 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,3,7,11} := rep015 halph

theorem query160 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,7,10,11} :=
  obstruction_transport link64 FastDual64_015.points {0,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep015 halph)

theorem rep016 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_016.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_016.pointList FastDual64_016.columns FastDual64_016.rows FastDual64_016.bound (by decide +kernel)
    FastDual64_016.column_mask FastDual64_016.checked hc F hF hroot hmin hout

theorem query106 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,3,9,10} := rep016 halph

theorem query312 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {2,3,10,11} :=
  obstruction_transport link64 FastDual64_016.points {2,3,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep016 halph)

theorem rep017 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_017.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_017.pointList FastDual64_017.columns FastDual64_017.rows FastDual64_017.bound (by decide +kernel)
    FastDual64_017.column_mask FastDual64_017.checked hc F hF hroot hmin hout

theorem query136 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,5,7,9} := rep017 halph

theorem query342 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {2,5,7,11} :=
  obstruction_transport link64 FastDual64_017.points {2,5,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep017 halph)

theorem rep018 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_018.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_018.pointList FastDual64_018.columns FastDual64_018.rows FastDual64_018.bound (by decide +kernel)
    FastDual64_018.column_mask FastDual64_018.checked hc F hF hroot hmin hout

theorem query137 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,5,7,10} := rep018 halph

theorem query398 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {3,5,7,11} :=
  obstruction_transport link64 FastDual64_018.points {3,5,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep018 halph)

theorem rep019 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_019.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_019.pointList FastDual64_019.columns FastDual64_019.rows FastDual64_019.bound (by decide +kernel)
    FastDual64_019.column_mask FastDual64_019.checked hc F hF hroot hmin hout

theorem query138 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,5,7,11} := rep019 halph

theorem rep020 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_020.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_020.pointList FastDual64_020.columns FastDual64_020.rows FastDual64_020.bound (by decide +kernel)
    FastDual64_020.column_mask FastDual64_020.checked hc F hF hroot hmin hout

theorem query142 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,5,9,10} := rep020 halph

theorem query297 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {2,3,5,11} :=
  obstruction_transport link64 FastDual64_020.points {2,3,5,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep020 halph)

theorem rep021 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_021.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_021.pointList FastDual64_021.columns FastDual64_021.rows FastDual64_021.bound (by decide +kernel)
    FastDual64_021.column_mask FastDual64_021.checked hc F hF hroot hmin hout

theorem query158 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {0,7,9,10} := rep021 halph

theorem query306 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {2,3,7,11} :=
  obstruction_transport link64 FastDual64_021.points {2,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep021 halph)

theorem rep022 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_022.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_022.pointList FastDual64_022.columns FastDual64_022.rows FastDual64_022.bound (by decide +kernel)
    FastDual64_022.column_mask FastDual64_022.checked hc F hF hroot hmin hout

theorem query295 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {2,3,5,9} := rep022 halph

theorem query346 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {2,5,9,10} :=
  obstruction_transport link64 FastDual64_022.points {2,5,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep022 halph)

theorem rep023 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_023.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_023.pointList FastDual64_023.columns FastDual64_023.rows FastDual64_023.bound (by decide +kernel)
    FastDual64_023.column_mask FastDual64_023.checked hc F hF hroot hmin hout

theorem query296 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {2,3,5,10} := rep023 halph

theorem query402 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {3,5,9,10} :=
  obstruction_transport link64 FastDual64_023.points {3,5,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep023 halph)

theorem rep024 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_024.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_024.pointList FastDual64_024.columns FastDual64_024.rows FastDual64_024.bound (by decide +kernel)
    FastDual64_024.column_mask FastDual64_024.checked hc F hF hroot hmin hout

theorem query304 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {2,3,7,9} := rep024 halph

theorem query362 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {2,7,9,10} :=
  obstruction_transport link64 FastDual64_024.points {2,7,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep024 halph)

theorem rep025 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_025.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_025.pointList FastDual64_025.columns FastDual64_025.rows FastDual64_025.bound (by decide +kernel)
    FastDual64_025.column_mask FastDual64_025.checked hc F hF hroot hmin hout

theorem query305 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {2,3,7,10} := rep025 halph

theorem query418 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {3,7,9,10} :=
  obstruction_transport link64 FastDual64_025.points {3,7,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep025 halph)

theorem rep026 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_026.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_026.pointList FastDual64_026.columns FastDual64_026.rows FastDual64_026.bound (by decide +kernel)
    FastDual64_026.column_mask FastDual64_026.checked hc F hF hroot hmin hout

theorem query340 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {2,5,7,9} := rep026 halph

theorem rep027 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_027.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_027.pointList FastDual64_027.columns FastDual64_027.rows FastDual64_027.bound (by decide +kernel)
    FastDual64_027.column_mask FastDual64_027.checked hc F hF hroot hmin hout

theorem query341 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {2,5,7,10} := rep027 halph

theorem query396 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {3,5,7,9} :=
  obstruction_transport link64 FastDual64_027.points {3,5,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep027 halph)

theorem rep028 (halph : AlphabetComplete link64 alphabets) :
    ActualObstruction link64 FastDual64_028.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link64 rootCodes root_binding alphabets halph nonincident_complete
    FastDual64_028.pointList FastDual64_028.columns FastDual64_028.rows FastDual64_028.bound (by decide +kernel)
    FastDual64_028.column_mask FastDual64_028.checked hc F hF hroot hmin hout

theorem query397 (halph : AlphabetComplete link64 alphabets) : ActualObstruction link64 {3,5,7,10} := rep028 halph

def dualQuads : List (Finset Point) := [{0,2,3,5},{5,9,10,11},{0,2,3,11},{0,9,10,11},{0,2,5,7},{5,7,9,11},{0,2,5,9},{2,5,9,11},{0,2,5,10},{3,5,9,11},{0,2,5,11},{0,5,9,11},{0,2,7,9},{2,7,9,11},{0,2,7,10},{3,7,9,11},{0,2,7,11},{0,7,9,11},{0,2,9,11},{0,3,5,9},{2,5,10,11},{0,3,5,10},{3,5,10,11},{0,3,5,11},{0,5,10,11},{0,3,7,9},{2,7,10,11},{0,3,7,10},{3,7,10,11},{0,3,7,11},{0,7,10,11},{0,3,9,10},{2,3,10,11},{0,5,7,9},{2,5,7,11},{0,5,7,10},{3,5,7,11},{0,5,7,11},{0,5,9,10},{2,3,5,11},{0,7,9,10},{2,3,7,11},{2,3,5,9},{2,5,9,10},{2,3,5,10},{3,5,9,10},{2,3,7,9},{2,7,9,10},{2,3,7,10},{3,7,9,10},{2,5,7,9},{2,5,7,10},{3,5,7,9},{3,5,7,10}]

theorem dual_actual (halph : AlphabetComplete link64 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link64 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query046 halph
  · exact query479 halph
  · exact query052 halph
  · exact query164 halph
  · exact query061 halph
  · exact query474 halph
  · exact query063 halph
  · exact query347 halph
  · exact query064 halph
  · exact query403 halph
  · exact query065 halph
  · exact query143 halph
  · exact query072 halph
  · exact query363 halph
  · exact query073 halph
  · exact query419 halph
  · exact query074 halph
  · exact query159 halph
  · exact query079 halph
  · exact query091 halph
  · exact query348 halph
  · exact query092 halph
  · exact query404 halph
  · exact query093 halph
  · exact query144 halph
  · exact query100 halph
  · exact query364 halph
  · exact query101 halph
  · exact query420 halph
  · exact query102 halph
  · exact query160 halph
  · exact query106 halph
  · exact query312 halph
  · exact query136 halph
  · exact query342 halph
  · exact query137 halph
  · exact query398 halph
  · exact query138 halph
  · exact query142 halph
  · exact query297 halph
  · exact query158 halph
  · exact query306 halph
  · exact query295 halph
  · exact query346 halph
  · exact query296 halph
  · exact query402 halph
  · exact query304 halph
  · exact query362 halph
  · exact query305 halph
  · exact query418 halph
  · exact query340 halph
  · exact query341 halph
  · exact query396 halph
  · exact query397 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link64 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link64 Q :=
  class_census link64 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source64
