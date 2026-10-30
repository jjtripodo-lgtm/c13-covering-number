import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source63
import C13Global.FastGroups.Source63Part00
import C13Global.FastGroups.Source63Part01
namespace C13.Global.Relative.Source63
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source63
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link63 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link63 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link63 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link63 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link63 alphabets) :
    ActualObstruction link63 FastDual63_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link63 rootCodes root_binding alphabets halph nonincident_complete
    FastDual63_000.pointList FastDual63_000.columns FastDual63_000.rows FastDual63_000.bound (by decide +kernel)
    FastDual63_000.column_mask FastDual63_000.checked hc F hF hroot hmin hout

theorem query046 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,2,3,5} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![0,1,3,2,8,9,11,10,4,5,7,6,12]
  invFun := ![0,1,3,2,8,9,11,10,4,5,7,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link63 = link63 :=
  root_symmetry_of_codes rootCodes link63 root_binding automorphism000 (by decide +kernel)

theorem query050 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,2,3,9} :=
  obstruction_transport link63 FastDual63_000.points {0,2,3,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

def automorphism001 : Equiv.Perm Point where
  toFun := ![5,4,7,6,1,0,3,2,8,9,10,11,12]
  invFun := ![5,4,7,6,1,0,3,2,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism001_hole : automorphism001 hole = hole := by decide +kernel

theorem automorphism001_root : transport automorphism001 link63 = link63 :=
  root_symmetry_of_codes rootCodes link63 root_binding automorphism001 (by decide +kernel)

theorem query130 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,5,6,7} :=
  obstruction_transport link63 FastDual63_000.points {0,5,6,7} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep000 halph)

def automorphism002 : Equiv.Perm Point where
  toFun := ![9,8,11,10,1,0,3,2,4,5,6,7,12]
  invFun := ![5,4,7,6,8,9,10,11,1,0,3,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism002_hole : automorphism002 hole = hole := by decide +kernel

theorem automorphism002_root : transport automorphism002 link63 = link63 :=
  root_symmetry_of_codes rootCodes link63 root_binding automorphism002 (by decide +kernel)

theorem query164 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,9,10,11} :=
  obstruction_transport link63 FastDual63_000.points {0,9,10,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep000 halph)

def automorphism003 : Equiv.Perm Point where
  toFun := ![5,4,7,6,8,9,10,11,1,0,3,2,12]
  invFun := ![9,8,11,10,1,0,3,2,4,5,6,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism003_hole : automorphism003 hole = hole := by decide +kernel

theorem automorphism003_root : transport automorphism003 link63 = link63 :=
  root_symmetry_of_codes rootCodes link63 root_binding automorphism003 (by decide +kernel)

theorem query461 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {5,6,7,9} :=
  obstruction_transport link63 FastDual63_000.points {5,6,7,9} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep000 halph)

def automorphism004 : Equiv.Perm Point where
  toFun := ![9,8,11,10,4,5,6,7,1,0,3,2,12]
  invFun := ![9,8,11,10,4,5,6,7,1,0,3,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism004_hole : automorphism004 hole = hole := by decide +kernel

theorem automorphism004_root : transport automorphism004 link63 = link63 :=
  root_symmetry_of_codes rootCodes link63 root_binding automorphism004 (by decide +kernel)

theorem query479 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {5,9,10,11} :=
  obstruction_transport link63 FastDual63_000.points {5,9,10,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link63 alphabets) :
    ActualObstruction link63 FastDual63_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link63 rootCodes root_binding alphabets halph nonincident_complete
    FastDual63_001.pointList FastDual63_001.columns FastDual63_001.rows FastDual63_001.bound (by decide +kernel)
    FastDual63_001.column_mask FastDual63_001.checked hc F hF hroot hmin hout

theorem query061 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,2,5,7} := rep001 halph

theorem query079 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,2,9,11} :=
  obstruction_transport link63 FastDual63_001.points {0,2,9,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep001 halph)

def automorphism005 : Equiv.Perm Point where
  toFun := ![5,4,6,7,1,0,2,3,8,9,11,10,12]
  invFun := ![5,4,6,7,1,0,2,3,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism005_hole : automorphism005 hole = hole := by decide +kernel

theorem automorphism005_root : transport automorphism005 link63 = link63 :=
  root_symmetry_of_codes rootCodes link63 root_binding automorphism005 (by decide +kernel)

theorem query088 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,3,5,6} :=
  obstruction_transport link63 FastDual63_001.points {0,3,5,6} automorphism005
    automorphism005_hole automorphism005_root (by decide +kernel) (rep001 halph)

def automorphism006 : Equiv.Perm Point where
  toFun := ![9,8,10,11,1,0,2,3,4,5,7,6,12]
  invFun := ![5,4,6,7,8,9,11,10,1,0,2,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism006_hole : automorphism006 hole = hole := by decide +kernel

theorem automorphism006_root : transport automorphism006 link63 = link63 :=
  root_symmetry_of_codes rootCodes link63 root_binding automorphism006 (by decide +kernel)

theorem query106 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,3,9,10} :=
  obstruction_transport link63 FastDual63_001.points {0,3,9,10} automorphism006
    automorphism006_hole automorphism006_root (by decide +kernel) (rep001 halph)

def automorphism007 : Equiv.Perm Point where
  toFun := ![9,8,10,11,4,5,7,6,1,0,2,3,12]
  invFun := ![9,8,10,11,4,5,7,6,1,0,2,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism007_hole : automorphism007 hole = hole := by decide +kernel

theorem automorphism007_root : transport automorphism007 link63 = link63 :=
  root_symmetry_of_codes rootCodes link63 root_binding automorphism007 (by decide +kernel)

theorem query467 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {5,6,9,10} :=
  obstruction_transport link63 FastDual63_001.points {5,6,9,10} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep001 halph)

theorem query474 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {5,7,9,11} :=
  obstruction_transport link63 FastDual63_001.points {5,7,9,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link63 alphabets) :
    ActualObstruction link63 FastDual63_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link63 rootCodes root_binding alphabets halph nonincident_complete
    FastDual63_002.pointList FastDual63_002.columns FastDual63_002.rows FastDual63_002.bound (by decide +kernel)
    FastDual63_002.column_mask FastDual63_002.checked hc F hF hroot hmin hout

theorem query063 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,2,5,9} := rep002 halph

theorem query091 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,3,5,9} :=
  obstruction_transport link63 FastDual63_002.points {0,3,5,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

def automorphism008 : Equiv.Perm Point where
  toFun := ![5,4,6,7,8,9,11,10,1,0,2,3,12]
  invFun := ![9,8,10,11,1,0,2,3,4,5,7,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism008_hole : automorphism008 hole = hole := by decide +kernel

theorem automorphism008_root : transport automorphism008 link63 = link63 :=
  root_symmetry_of_codes rootCodes link63 root_binding automorphism008 (by decide +kernel)

theorem query132 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,5,6,9} :=
  obstruction_transport link63 FastDual63_002.points {0,5,6,9} automorphism008
    automorphism008_hole automorphism008_root (by decide +kernel) (rep002 halph)

theorem query136 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,5,7,9} :=
  obstruction_transport link63 FastDual63_002.points {0,5,7,9} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep002 halph)

theorem query142 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,5,9,10} :=
  obstruction_transport link63 FastDual63_002.points {0,5,9,10} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep002 halph)

theorem query143 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,5,9,11} :=
  obstruction_transport link63 FastDual63_002.points {0,5,9,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link63 alphabets) :
    ActualObstruction link63 FastDual63_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link63 rootCodes root_binding alphabets halph nonincident_complete
    FastDual63_003.pointList FastDual63_003.columns FastDual63_003.rows FastDual63_003.bound (by decide +kernel)
    FastDual63_003.column_mask FastDual63_003.checked hc F hF hroot hmin hout

theorem query064 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,2,5,10} := rep003 halph

def automorphism009 : Equiv.Perm Point where
  toFun := ![0,1,2,3,8,9,10,11,4,5,6,7,12]
  invFun := ![0,1,2,3,8,9,10,11,4,5,6,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism009_hole : automorphism009 hole = hole := by decide +kernel

theorem automorphism009_root : transport automorphism009 link63 = link63 :=
  root_symmetry_of_codes rootCodes link63 root_binding automorphism009 (by decide +kernel)

theorem query068 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,2,6,9} :=
  obstruction_transport link63 FastDual63_003.points {0,2,6,9} automorphism009
    automorphism009_hole automorphism009_root (by decide +kernel) (rep003 halph)

def automorphism010 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism010_hole : automorphism010 hole = hole := by decide +kernel

theorem automorphism010_root : transport automorphism010 link63 = link63 :=
  root_symmetry_of_codes rootCodes link63 root_binding automorphism010 (by decide +kernel)

theorem query093 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,3,5,11} :=
  obstruction_transport link63 FastDual63_003.points {0,3,5,11} automorphism010
    automorphism010_hole automorphism010_root (by decide +kernel) (rep003 halph)

theorem query100 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,3,7,9} :=
  obstruction_transport link63 FastDual63_003.points {0,3,7,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem query134 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,5,6,11} :=
  obstruction_transport link63 FastDual63_003.points {0,5,6,11} automorphism005
    automorphism005_hole automorphism005_root (by decide +kernel) (rep003 halph)

theorem query137 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,5,7,10} :=
  obstruction_transport link63 FastDual63_003.points {0,5,7,10} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep003 halph)

theorem query153 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,6,9,11} :=
  obstruction_transport link63 FastDual63_003.points {0,6,9,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep003 halph)

theorem query158 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,7,9,10} :=
  obstruction_transport link63 FastDual63_003.points {0,7,9,10} automorphism006
    automorphism006_hole automorphism006_root (by decide +kernel) (rep003 halph)

theorem query336 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,5,6,9} :=
  obstruction_transport link63 FastDual63_003.points {2,5,6,9} automorphism008
    automorphism008_hole automorphism008_root (by decide +kernel) (rep003 halph)

theorem query346 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,5,9,10} :=
  obstruction_transport link63 FastDual63_003.points {2,5,9,10} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep003 halph)

theorem query396 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,5,7,9} :=
  obstruction_transport link63 FastDual63_003.points {3,5,7,9} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep003 halph)

theorem query403 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,5,9,11} :=
  obstruction_transport link63 FastDual63_003.points {3,5,9,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link63 alphabets) :
    ActualObstruction link63 FastDual63_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link63 rootCodes root_binding alphabets halph nonincident_complete
    FastDual63_004.pointList FastDual63_004.columns FastDual63_004.rows FastDual63_004.bound (by decide +kernel)
    FastDual63_004.column_mask FastDual63_004.checked hc F hF hroot hmin hout

theorem query065 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,2,5,11} := rep004 halph

theorem query072 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,2,7,9} :=
  obstruction_transport link63 FastDual63_004.points {0,2,7,9} automorphism009
    automorphism009_hole automorphism009_root (by decide +kernel) (rep004 halph)

theorem query092 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,3,5,10} :=
  obstruction_transport link63 FastDual63_004.points {0,3,5,10} automorphism010
    automorphism010_hole automorphism010_root (by decide +kernel) (rep004 halph)

theorem query096 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,3,6,9} :=
  obstruction_transport link63 FastDual63_004.points {0,3,6,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep004 halph)

theorem query133 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,5,6,10} :=
  obstruction_transport link63 FastDual63_004.points {0,5,6,10} automorphism005
    automorphism005_hole automorphism005_root (by decide +kernel) (rep004 halph)

theorem query138 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,5,7,11} :=
  obstruction_transport link63 FastDual63_004.points {0,5,7,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep004 halph)

theorem query152 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,6,9,10} :=
  obstruction_transport link63 FastDual63_004.points {0,6,9,10} automorphism006
    automorphism006_hole automorphism006_root (by decide +kernel) (rep004 halph)

theorem query159 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,7,9,11} :=
  obstruction_transport link63 FastDual63_004.points {0,7,9,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep004 halph)

theorem query340 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,5,7,9} :=
  obstruction_transport link63 FastDual63_004.points {2,5,7,9} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep004 halph)

theorem query347 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,5,9,11} :=
  obstruction_transport link63 FastDual63_004.points {2,5,9,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep004 halph)

theorem query392 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,5,6,9} :=
  obstruction_transport link63 FastDual63_004.points {3,5,6,9} automorphism008
    automorphism008_hole automorphism008_root (by decide +kernel) (rep004 halph)

theorem query402 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,5,9,10} :=
  obstruction_transport link63 FastDual63_004.points {3,5,9,10} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep004 halph)

theorem rep005 (halph : AlphabetComplete link63 alphabets) :
    ActualObstruction link63 FastDual63_005.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link63 rootCodes root_binding alphabets halph nonincident_complete
    FastDual63_005.pointList FastDual63_005.columns FastDual63_005.rows FastDual63_005.bound (by decide +kernel)
    FastDual63_005.column_mask FastDual63_005.checked hc F hF hroot hmin hout

theorem query069 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,2,6,10} := rep005 halph

theorem query102 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,3,7,11} :=
  obstruction_transport link63 FastDual63_005.points {0,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep005 halph)

theorem query338 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,5,6,11} :=
  obstruction_transport link63 FastDual63_005.points {2,5,6,11} automorphism008
    automorphism008_hole automorphism008_root (by decide +kernel) (rep005 halph)

theorem query362 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,7,9,10} :=
  obstruction_transport link63 FastDual63_005.points {2,7,9,10} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep005 halph)

theorem query397 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,5,7,10} :=
  obstruction_transport link63 FastDual63_005.points {3,5,7,10} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep005 halph)

theorem query413 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,6,9,11} :=
  obstruction_transport link63 FastDual63_005.points {3,6,9,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep005 halph)

theorem rep006 (halph : AlphabetComplete link63 alphabets) :
    ActualObstruction link63 FastDual63_006.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link63 rootCodes root_binding alphabets halph nonincident_complete
    FastDual63_006.pointList FastDual63_006.columns FastDual63_006.rows FastDual63_006.bound (by decide +kernel)
    FastDual63_006.column_mask FastDual63_006.checked hc F hF hroot hmin hout

theorem query070 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,2,6,11} := rep006 halph

theorem query073 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,2,7,10} :=
  obstruction_transport link63 FastDual63_006.points {0,2,7,10} automorphism009
    automorphism009_hole automorphism009_root (by decide +kernel) (rep006 halph)

theorem query098 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,3,6,11} :=
  obstruction_transport link63 FastDual63_006.points {0,3,6,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep006 halph)

theorem query101 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,3,7,10} :=
  obstruction_transport link63 FastDual63_006.points {0,3,7,10} automorphism010
    automorphism010_hole automorphism010_root (by decide +kernel) (rep006 halph)

theorem query337 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,5,6,10} :=
  obstruction_transport link63 FastDual63_006.points {2,5,6,10} automorphism005
    automorphism005_hole automorphism005_root (by decide +kernel) (rep006 halph)

theorem query341 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,5,7,10} :=
  obstruction_transport link63 FastDual63_006.points {2,5,7,10} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep006 halph)

theorem query356 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,6,9,10} :=
  obstruction_transport link63 FastDual63_006.points {2,6,9,10} automorphism006
    automorphism006_hole automorphism006_root (by decide +kernel) (rep006 halph)

theorem query357 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,6,9,11} :=
  obstruction_transport link63 FastDual63_006.points {2,6,9,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep006 halph)

theorem query394 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,5,6,11} :=
  obstruction_transport link63 FastDual63_006.points {3,5,6,11} automorphism008
    automorphism008_hole automorphism008_root (by decide +kernel) (rep006 halph)

theorem query398 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,5,7,11} :=
  obstruction_transport link63 FastDual63_006.points {3,5,7,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep006 halph)

theorem query418 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,7,9,10} :=
  obstruction_transport link63 FastDual63_006.points {3,7,9,10} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep006 halph)

theorem query419 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,7,9,11} :=
  obstruction_transport link63 FastDual63_006.points {3,7,9,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep006 halph)

theorem rep007 (halph : AlphabetComplete link63 alphabets) :
    ActualObstruction link63 FastDual63_007.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link63 rootCodes root_binding alphabets halph nonincident_complete
    FastDual63_007.pointList FastDual63_007.columns FastDual63_007.rows FastDual63_007.bound (by decide +kernel)
    FastDual63_007.column_mask FastDual63_007.checked hc F hF hroot hmin hout

theorem query074 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,2,7,11} := rep007 halph

theorem query097 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,3,6,10} :=
  obstruction_transport link63 FastDual63_007.points {0,3,6,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep007 halph)

theorem query342 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,5,7,11} :=
  obstruction_transport link63 FastDual63_007.points {2,5,7,11} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep007 halph)

theorem query363 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,7,9,11} :=
  obstruction_transport link63 FastDual63_007.points {2,7,9,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep007 halph)

theorem query393 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,5,6,10} :=
  obstruction_transport link63 FastDual63_007.points {3,5,6,10} automorphism008
    automorphism008_hole automorphism008_root (by decide +kernel) (rep007 halph)

theorem query412 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,6,9,10} :=
  obstruction_transport link63 FastDual63_007.points {3,6,9,10} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep007 halph)

theorem rep008 (halph : AlphabetComplete link63 alphabets) :
    ActualObstruction link63 FastDual63_008.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link63 rootCodes root_binding alphabets halph nonincident_complete
    FastDual63_008.pointList FastDual63_008.columns FastDual63_008.rows FastDual63_008.bound (by decide +kernel)
    FastDual63_008.column_mask FastDual63_008.checked hc F hF hroot hmin hout

theorem query144 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,5,10,11} := rep008 halph

theorem query146 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,6,7,9} :=
  obstruction_transport link63 FastDual63_008.points {0,6,7,9} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep008 halph)

theorem query295 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,3,5,9} :=
  obstruction_transport link63 FastDual63_008.points {2,3,5,9} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep008 halph)

theorem rep009 (halph : AlphabetComplete link63 alphabets) :
    ActualObstruction link63 FastDual63_009.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link63 rootCodes root_binding alphabets halph nonincident_complete
    FastDual63_009.pointList FastDual63_009.columns FastDual63_009.rows FastDual63_009.bound (by decide +kernel)
    FastDual63_009.column_mask FastDual63_009.checked hc F hF hroot hmin hout

theorem query147 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,6,7,10} := rep009 halph

theorem query148 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,6,7,11} :=
  obstruction_transport link63 FastDual63_009.points {0,6,7,11} automorphism010
    automorphism010_hole automorphism010_root (by decide +kernel) (rep009 halph)

theorem query154 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,6,10,11} :=
  obstruction_transport link63 FastDual63_009.points {0,6,10,11} automorphism009
    automorphism009_hole automorphism009_root (by decide +kernel) (rep009 halph)

theorem query160 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {0,7,10,11} :=
  obstruction_transport link63 FastDual63_009.points {0,7,10,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep009 halph)

theorem query296 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,3,5,10} :=
  obstruction_transport link63 FastDual63_009.points {2,3,5,10} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep009 halph)

theorem query297 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,3,5,11} :=
  obstruction_transport link63 FastDual63_009.points {2,3,5,11} automorphism005
    automorphism005_hole automorphism005_root (by decide +kernel) (rep009 halph)

theorem query300 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,3,6,9} :=
  obstruction_transport link63 FastDual63_009.points {2,3,6,9} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep009 halph)

theorem query304 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,3,7,9} :=
  obstruction_transport link63 FastDual63_009.points {2,3,7,9} automorphism006
    automorphism006_hole automorphism006_root (by decide +kernel) (rep009 halph)

theorem query348 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,5,10,11} :=
  obstruction_transport link63 FastDual63_009.points {2,5,10,11} automorphism008
    automorphism008_hole automorphism008_root (by decide +kernel) (rep009 halph)

theorem query350 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,6,7,9} :=
  obstruction_transport link63 FastDual63_009.points {2,6,7,9} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep009 halph)

theorem query404 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,5,10,11} :=
  obstruction_transport link63 FastDual63_009.points {3,5,10,11} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep009 halph)

theorem query406 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,6,7,9} :=
  obstruction_transport link63 FastDual63_009.points {3,6,7,9} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep009 halph)

theorem rep010 (halph : AlphabetComplete link63 alphabets) :
    ActualObstruction link63 FastDual63_010.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link63 rootCodes root_binding alphabets halph nonincident_complete
    FastDual63_010.pointList FastDual63_010.columns FastDual63_010.rows FastDual63_010.bound (by decide +kernel)
    FastDual63_010.column_mask FastDual63_010.checked hc F hF hroot hmin hout

theorem query298 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,3,6,7} := rep010 halph

theorem query312 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,3,10,11} :=
  obstruction_transport link63 FastDual63_010.points {2,3,10,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep010 halph)

theorem query485 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {6,7,10,11} :=
  obstruction_transport link63 FastDual63_010.points {6,7,10,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep010 halph)

theorem rep011 (halph : AlphabetComplete link63 alphabets) :
    ActualObstruction link63 FastDual63_011.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link63 rootCodes root_binding alphabets halph nonincident_complete
    FastDual63_011.pointList FastDual63_011.columns FastDual63_011.rows FastDual63_011.bound (by decide +kernel)
    FastDual63_011.column_mask FastDual63_011.checked hc F hF hroot hmin hout

theorem query301 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,3,6,10} := rep011 halph

theorem query306 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,3,7,11} :=
  obstruction_transport link63 FastDual63_011.points {2,3,7,11} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep011 halph)

theorem query352 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,6,7,11} :=
  obstruction_transport link63 FastDual63_011.points {2,6,7,11} automorphism008
    automorphism008_hole automorphism008_root (by decide +kernel) (rep011 halph)

theorem query364 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,7,10,11} :=
  obstruction_transport link63 FastDual63_011.points {2,7,10,11} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep011 halph)

theorem query407 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,6,7,10} :=
  obstruction_transport link63 FastDual63_011.points {3,6,7,10} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep011 halph)

theorem query414 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,6,10,11} :=
  obstruction_transport link63 FastDual63_011.points {3,6,10,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep011 halph)

theorem rep012 (halph : AlphabetComplete link63 alphabets) :
    ActualObstruction link63 FastDual63_012.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link63 rootCodes root_binding alphabets halph nonincident_complete
    FastDual63_012.pointList FastDual63_012.columns FastDual63_012.rows FastDual63_012.bound (by decide +kernel)
    FastDual63_012.column_mask FastDual63_012.checked hc F hF hroot hmin hout

theorem query302 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,3,6,11} := rep012 halph

theorem query305 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,3,7,10} :=
  obstruction_transport link63 FastDual63_012.points {2,3,7,10} automorphism009
    automorphism009_hole automorphism009_root (by decide +kernel) (rep012 halph)

theorem query351 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,6,7,10} :=
  obstruction_transport link63 FastDual63_012.points {2,6,7,10} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep012 halph)

theorem query358 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {2,6,10,11} :=
  obstruction_transport link63 FastDual63_012.points {2,6,10,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep012 halph)

theorem query408 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,6,7,11} :=
  obstruction_transport link63 FastDual63_012.points {3,6,7,11} automorphism008
    automorphism008_hole automorphism008_root (by decide +kernel) (rep012 halph)

theorem query420 (halph : AlphabetComplete link63 alphabets) : ActualObstruction link63 {3,7,10,11} :=
  obstruction_transport link63 FastDual63_012.points {3,7,10,11} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep012 halph)

def dualQuads : List (Finset Point) := [{0,2,3,5},{0,2,3,9},{0,5,6,7},{0,9,10,11},{5,6,7,9},{5,9,10,11},{0,2,5,7},{0,2,9,11},{0,3,5,6},{0,3,9,10},{5,6,9,10},{5,7,9,11},{0,2,5,9},{0,3,5,9},{0,5,6,9},{0,5,7,9},{0,5,9,10},{0,5,9,11},{0,2,5,10},{0,2,6,9},{0,3,5,11},{0,3,7,9},{0,5,6,11},{0,5,7,10},{0,6,9,11},{0,7,9,10},{2,5,6,9},{2,5,9,10},{3,5,7,9},{3,5,9,11},{0,2,5,11},{0,2,7,9},{0,3,5,10},{0,3,6,9},{0,5,6,10},{0,5,7,11},{0,6,9,10},{0,7,9,11},{2,5,7,9},{2,5,9,11},{3,5,6,9},{3,5,9,10},{0,2,6,10},{0,3,7,11},{2,5,6,11},{2,7,9,10},{3,5,7,10},{3,6,9,11},{0,2,6,11},{0,2,7,10},{0,3,6,11},{0,3,7,10},{2,5,6,10},{2,5,7,10},{2,6,9,10},{2,6,9,11},{3,5,6,11},{3,5,7,11},{3,7,9,10},{3,7,9,11},{0,2,7,11},{0,3,6,10},{2,5,7,11},{2,7,9,11},{3,5,6,10},{3,6,9,10},{0,5,10,11},{0,6,7,9},{2,3,5,9},{0,6,7,10},{0,6,7,11},{0,6,10,11},{0,7,10,11},{2,3,5,10},{2,3,5,11},{2,3,6,9},{2,3,7,9},{2,5,10,11},{2,6,7,9},{3,5,10,11},{3,6,7,9},{2,3,6,7},{2,3,10,11},{6,7,10,11},{2,3,6,10},{2,3,7,11},{2,6,7,11},{2,7,10,11},{3,6,7,10},{3,6,10,11},{2,3,6,11},{2,3,7,10},{2,6,7,10},{2,6,10,11},{3,6,7,11},{3,7,10,11}]

theorem dual_actual (halph : AlphabetComplete link63 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link63 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query046 halph
  · exact query050 halph
  · exact query130 halph
  · exact query164 halph
  · exact query461 halph
  · exact query479 halph
  · exact query061 halph
  · exact query079 halph
  · exact query088 halph
  · exact query106 halph
  · exact query467 halph
  · exact query474 halph
  · exact query063 halph
  · exact query091 halph
  · exact query132 halph
  · exact query136 halph
  · exact query142 halph
  · exact query143 halph
  · exact query064 halph
  · exact query068 halph
  · exact query093 halph
  · exact query100 halph
  · exact query134 halph
  · exact query137 halph
  · exact query153 halph
  · exact query158 halph
  · exact query336 halph
  · exact query346 halph
  · exact query396 halph
  · exact query403 halph
  · exact query065 halph
  · exact query072 halph
  · exact query092 halph
  · exact query096 halph
  · exact query133 halph
  · exact query138 halph
  · exact query152 halph
  · exact query159 halph
  · exact query340 halph
  · exact query347 halph
  · exact query392 halph
  · exact query402 halph
  · exact query069 halph
  · exact query102 halph
  · exact query338 halph
  · exact query362 halph
  · exact query397 halph
  · exact query413 halph
  · exact query070 halph
  · exact query073 halph
  · exact query098 halph
  · exact query101 halph
  · exact query337 halph
  · exact query341 halph
  · exact query356 halph
  · exact query357 halph
  · exact query394 halph
  · exact query398 halph
  · exact query418 halph
  · exact query419 halph
  · exact query074 halph
  · exact query097 halph
  · exact query342 halph
  · exact query363 halph
  · exact query393 halph
  · exact query412 halph
  · exact query144 halph
  · exact query146 halph
  · exact query295 halph
  · exact query147 halph
  · exact query148 halph
  · exact query154 halph
  · exact query160 halph
  · exact query296 halph
  · exact query297 halph
  · exact query300 halph
  · exact query304 halph
  · exact query348 halph
  · exact query350 halph
  · exact query404 halph
  · exact query406 halph
  · exact query298 halph
  · exact query312 halph
  · exact query485 halph
  · exact query301 halph
  · exact query306 halph
  · exact query352 halph
  · exact query364 halph
  · exact query407 halph
  · exact query414 halph
  · exact query302 halph
  · exact query305 halph
  · exact query351 halph
  · exact query358 halph
  · exact query408 halph
  · exact query420 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link63 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link63 Q :=
  class_census link63 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source63
