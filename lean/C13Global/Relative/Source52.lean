import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source52
import C13Global.FastGroups.Source52Part00
namespace C13.Global.Relative.Source52
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source52
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link52 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete link52 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction link52 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction link52 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete link52 alphabets) :
    ActualObstruction link52 FastDual52_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link52 rootCodes root_binding alphabets halph nonincident_complete
    FastDual52_000.pointList FastDual52_000.columns FastDual52_000.rows FastDual52_000.bound (by decide +kernel)
    FastDual52_000.column_mask FastDual52_000.checked hc F hF hroot hmin hout

theorem query180 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,2,5,6} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![8,10,9,11,0,2,1,3,4,6,5,7,12]
  invFun := ![4,6,5,7,8,10,9,11,0,2,1,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism000 (by decide +kernel)

theorem query198 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,2,9,10} :=
  obstruction_transport link52 FastDual52_000.points {1,2,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

def automorphism001 : Equiv.Perm Point where
  toFun := ![4,7,5,6,0,3,1,2,8,11,9,10,12]
  invFun := ![4,6,7,5,0,2,3,1,8,10,11,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism001_hole : automorphism001 hole = hole := by decide +kernel

theorem automorphism001_root : transport automorphism001 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism001 (by decide +kernel)

theorem query209 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,3,5,7} :=
  obstruction_transport link52 FastDual52_000.points {1,3,5,7} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep000 halph)

def automorphism002 : Equiv.Perm Point where
  toFun := ![8,11,9,10,0,3,1,2,4,7,5,6,12]
  invFun := ![4,6,7,5,8,10,11,9,0,2,3,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism002_hole : automorphism002 hole = hole := by decide +kernel

theorem automorphism002_root : transport automorphism002 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism002 (by decide +kernel)

theorem query227 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,3,9,11} :=
  obstruction_transport link52 FastDual52_000.points {1,3,9,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep000 halph)

def automorphism003 : Equiv.Perm Point where
  toFun := ![4,7,6,5,0,3,2,1,8,11,10,9,12]
  invFun := ![4,7,6,5,0,3,2,1,8,11,10,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism003_hole : automorphism003 hole = hole := by decide +kernel

theorem automorphism003_root : transport automorphism003 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism003 (by decide +kernel)

theorem query298 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,3,6,7} :=
  obstruction_transport link52 FastDual52_000.points {2,3,6,7} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep000 halph)

def automorphism004 : Equiv.Perm Point where
  toFun := ![8,11,10,9,0,3,2,1,4,7,6,5,12]
  invFun := ![4,7,6,5,8,11,10,9,0,3,2,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism004_hole : automorphism004 hole = hole := by decide +kernel

theorem automorphism004_root : transport automorphism004 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism004 (by decide +kernel)

theorem query312 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,3,10,11} :=
  obstruction_transport link52 FastDual52_000.points {2,3,10,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep000 halph)

def automorphism005 : Equiv.Perm Point where
  toFun := ![8,10,9,11,4,6,5,7,0,2,1,3,12]
  invFun := ![8,10,9,11,4,6,5,7,0,2,1,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism005_hole : automorphism005 hole = hole := by decide +kernel

theorem automorphism005_root : transport automorphism005 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism005 (by decide +kernel)

theorem query467 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {5,6,9,10} :=
  obstruction_transport link52 FastDual52_000.points {5,6,9,10} automorphism005
    automorphism005_hole automorphism005_root (by decide +kernel) (rep000 halph)

def automorphism006 : Equiv.Perm Point where
  toFun := ![8,11,9,10,4,7,5,6,0,3,1,2,12]
  invFun := ![8,10,11,9,4,6,7,5,0,2,3,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism006_hole : automorphism006 hole = hole := by decide +kernel

theorem automorphism006_root : transport automorphism006 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism006 (by decide +kernel)

theorem query474 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {5,7,9,11} :=
  obstruction_transport link52 FastDual52_000.points {5,7,9,11} automorphism006
    automorphism006_hole automorphism006_root (by decide +kernel) (rep000 halph)

def automorphism007 : Equiv.Perm Point where
  toFun := ![8,11,10,9,4,7,6,5,0,3,2,1,12]
  invFun := ![8,11,10,9,4,7,6,5,0,3,2,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism007_hole : automorphism007 hole = hole := by decide +kernel

theorem automorphism007_root : transport automorphism007 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism007 (by decide +kernel)

theorem query485 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {6,7,10,11} :=
  obstruction_transport link52 FastDual52_000.points {6,7,10,11} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete link52 alphabets) :
    ActualObstruction link52 FastDual52_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link52 rootCodes root_binding alphabets halph nonincident_complete
    FastDual52_001.pointList FastDual52_001.columns FastDual52_001.rows FastDual52_001.bound (by decide +kernel)
    FastDual52_001.column_mask FastDual52_001.checked hc F hF hroot hmin hout

theorem query183 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,2,5,9} := rep001 halph

def automorphism008 : Equiv.Perm Point where
  toFun := ![0,2,1,3,8,10,9,11,4,6,5,7,12]
  invFun := ![0,2,1,3,8,10,9,11,4,6,5,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism008_hole : automorphism008 hole = hole := by decide +kernel

theorem automorphism008_root : transport automorphism008 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism008 (by decide +kernel)

theorem query189 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,2,6,10} :=
  obstruction_transport link52 FastDual52_001.points {1,2,6,10} automorphism008
    automorphism008_hole automorphism008_root (by decide +kernel) (rep001 halph)

def automorphism009 : Equiv.Perm Point where
  toFun := ![0,1,3,2,8,9,11,10,4,5,7,6,12]
  invFun := ![0,1,3,2,8,9,11,10,4,5,7,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism009_hole : automorphism009 hole = hole := by decide +kernel

theorem automorphism009_root : transport automorphism009 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism009 (by decide +kernel)

theorem query211 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,3,5,9} :=
  obstruction_transport link52 FastDual52_001.points {1,3,5,9} automorphism009
    automorphism009_hole automorphism009_root (by decide +kernel) (rep001 halph)

def automorphism010 : Equiv.Perm Point where
  toFun := ![0,3,1,2,8,11,9,10,4,7,5,6,12]
  invFun := ![0,2,3,1,8,10,11,9,4,6,7,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism010_hole : automorphism010 hole = hole := by decide +kernel

theorem automorphism010_root : transport automorphism010 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism010 (by decide +kernel)

theorem query222 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,3,7,11} :=
  obstruction_transport link52 FastDual52_001.points {1,3,7,11} automorphism010
    automorphism010_hole automorphism010_root (by decide +kernel) (rep001 halph)

def automorphism011 : Equiv.Perm Point where
  toFun := ![4,5,6,7,8,9,10,11,0,1,2,3,12]
  invFun := ![8,9,10,11,0,1,2,3,4,5,6,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism011_hole : automorphism011 hole = hole := by decide +kernel

theorem automorphism011_root : transport automorphism011 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism011 (by decide +kernel)

theorem query252 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,5,6,9} :=
  obstruction_transport link52 FastDual52_001.points {1,5,6,9} automorphism011
    automorphism011_hole automorphism011_root (by decide +kernel) (rep001 halph)

def automorphism012 : Equiv.Perm Point where
  toFun := ![4,5,7,6,8,9,11,10,0,1,3,2,12]
  invFun := ![8,9,11,10,0,1,3,2,4,5,7,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism012_hole : automorphism012 hole = hole := by decide +kernel

theorem automorphism012_root : transport automorphism012 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism012 (by decide +kernel)

theorem query256 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,5,7,9} :=
  obstruction_transport link52 FastDual52_001.points {1,5,7,9} automorphism012
    automorphism012_hole automorphism012_root (by decide +kernel) (rep001 halph)

def automorphism013 : Equiv.Perm Point where
  toFun := ![8,9,10,11,4,5,6,7,0,1,2,3,12]
  invFun := ![8,9,10,11,4,5,6,7,0,1,2,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism013_hole : automorphism013 hole = hole := by decide +kernel

theorem automorphism013_root : transport automorphism013 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism013 (by decide +kernel)

theorem query262 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,5,9,10} :=
  obstruction_transport link52 FastDual52_001.points {1,5,9,10} automorphism013
    automorphism013_hole automorphism013_root (by decide +kernel) (rep001 halph)

def automorphism014 : Equiv.Perm Point where
  toFun := ![8,9,11,10,4,5,7,6,0,1,3,2,12]
  invFun := ![8,9,11,10,4,5,7,6,0,1,3,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism014_hole : automorphism014 hole = hole := by decide +kernel

theorem automorphism014_root : transport automorphism014 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism014 (by decide +kernel)

theorem query263 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,5,9,11} :=
  obstruction_transport link52 FastDual52_001.points {1,5,9,11} automorphism014
    automorphism014_hole automorphism014_root (by decide +kernel) (rep001 halph)

def automorphism015 : Equiv.Perm Point where
  toFun := ![0,2,3,1,8,10,11,9,4,6,7,5,12]
  invFun := ![0,3,1,2,8,11,9,10,4,7,5,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism015_hole : automorphism015 hole = hole := by decide +kernel

theorem automorphism015_root : transport automorphism015 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism015 (by decide +kernel)

theorem query301 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,3,6,10} :=
  obstruction_transport link52 FastDual52_001.points {2,3,6,10} automorphism015
    automorphism015_hole automorphism015_root (by decide +kernel) (rep001 halph)

def automorphism016 : Equiv.Perm Point where
  toFun := ![0,3,2,1,8,11,10,9,4,7,6,5,12]
  invFun := ![0,3,2,1,8,11,10,9,4,7,6,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism016_hole : automorphism016 hole = hole := by decide +kernel

theorem automorphism016_root : transport automorphism016 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism016 (by decide +kernel)

theorem query306 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,3,7,11} :=
  obstruction_transport link52 FastDual52_001.points {2,3,7,11} automorphism016
    automorphism016_hole automorphism016_root (by decide +kernel) (rep001 halph)

def automorphism017 : Equiv.Perm Point where
  toFun := ![4,6,5,7,8,10,9,11,0,2,1,3,12]
  invFun := ![8,10,9,11,0,2,1,3,4,6,5,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism017_hole : automorphism017 hole = hole := by decide +kernel

theorem automorphism017_root : transport automorphism017 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism017 (by decide +kernel)

theorem query337 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,5,6,10} :=
  obstruction_transport link52 FastDual52_001.points {2,5,6,10} automorphism017
    automorphism017_hole automorphism017_root (by decide +kernel) (rep001 halph)

def automorphism018 : Equiv.Perm Point where
  toFun := ![4,6,7,5,8,10,11,9,0,2,3,1,12]
  invFun := ![8,11,9,10,0,3,1,2,4,7,5,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism018_hole : automorphism018 hole = hole := by decide +kernel

theorem automorphism018_root : transport automorphism018 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism018 (by decide +kernel)

theorem query351 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,6,7,10} :=
  obstruction_transport link52 FastDual52_001.points {2,6,7,10} automorphism018
    automorphism018_hole automorphism018_root (by decide +kernel) (rep001 halph)

theorem query356 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,6,9,10} :=
  obstruction_transport link52 FastDual52_001.points {2,6,9,10} automorphism005
    automorphism005_hole automorphism005_root (by decide +kernel) (rep001 halph)

def automorphism019 : Equiv.Perm Point where
  toFun := ![8,10,11,9,4,6,7,5,0,2,3,1,12]
  invFun := ![8,11,9,10,4,7,5,6,0,3,1,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism019_hole : automorphism019 hole = hole := by decide +kernel

theorem automorphism019_root : transport automorphism019 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism019 (by decide +kernel)

theorem query358 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,6,10,11} :=
  obstruction_transport link52 FastDual52_001.points {2,6,10,11} automorphism019
    automorphism019_hole automorphism019_root (by decide +kernel) (rep001 halph)

def automorphism020 : Equiv.Perm Point where
  toFun := ![4,7,5,6,8,11,9,10,0,3,1,2,12]
  invFun := ![8,10,11,9,0,2,3,1,4,6,7,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism020_hole : automorphism020 hole = hole := by decide +kernel

theorem automorphism020_root : transport automorphism020 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism020 (by decide +kernel)

theorem query398 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,5,7,11} :=
  obstruction_transport link52 FastDual52_001.points {3,5,7,11} automorphism020
    automorphism020_hole automorphism020_root (by decide +kernel) (rep001 halph)

def automorphism021 : Equiv.Perm Point where
  toFun := ![4,7,6,5,8,11,10,9,0,3,2,1,12]
  invFun := ![8,11,10,9,0,3,2,1,4,7,6,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism021_hole : automorphism021 hole = hole := by decide +kernel

theorem automorphism021_root : transport automorphism021 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism021 (by decide +kernel)

theorem query408 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,6,7,11} :=
  obstruction_transport link52 FastDual52_001.points {3,6,7,11} automorphism021
    automorphism021_hole automorphism021_root (by decide +kernel) (rep001 halph)

theorem query419 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,7,9,11} :=
  obstruction_transport link52 FastDual52_001.points {3,7,9,11} automorphism006
    automorphism006_hole automorphism006_root (by decide +kernel) (rep001 halph)

theorem query420 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,7,10,11} :=
  obstruction_transport link52 FastDual52_001.points {3,7,10,11} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete link52 alphabets) :
    ActualObstruction link52 FastDual52_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link52 rootCodes root_binding alphabets halph nonincident_complete
    FastDual52_002.pointList FastDual52_002.columns FastDual52_002.rows FastDual52_002.bound (by decide +kernel)
    FastDual52_002.column_mask FastDual52_002.checked hc F hF hroot hmin hout

theorem query184 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,2,5,10} := rep002 halph

def automorphism022 : Equiv.Perm Point where
  toFun := ![0,1,2,3,8,9,10,11,4,5,6,7,12]
  invFun := ![0,1,2,3,8,9,10,11,4,5,6,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism022_hole : automorphism022 hole = hole := by decide +kernel

theorem automorphism022_root : transport automorphism022 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism022 (by decide +kernel)

theorem query188 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,2,6,9} :=
  obstruction_transport link52 FastDual52_002.points {1,2,6,9} automorphism022
    automorphism022_hole automorphism022_root (by decide +kernel) (rep002 halph)

theorem query213 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,3,5,11} :=
  obstruction_transport link52 FastDual52_002.points {1,3,5,11} automorphism010
    automorphism010_hole automorphism010_root (by decide +kernel) (rep002 halph)

theorem query220 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,3,7,9} :=
  obstruction_transport link52 FastDual52_002.points {1,3,7,9} automorphism009
    automorphism009_hole automorphism009_root (by decide +kernel) (rep002 halph)

theorem query253 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,5,6,10} :=
  obstruction_transport link52 FastDual52_002.points {1,5,6,10} automorphism017
    automorphism017_hole automorphism017_root (by decide +kernel) (rep002 halph)

theorem query258 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,5,7,11} :=
  obstruction_transport link52 FastDual52_002.points {1,5,7,11} automorphism020
    automorphism020_hole automorphism020_root (by decide +kernel) (rep002 halph)

theorem query272 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,6,9,10} :=
  obstruction_transport link52 FastDual52_002.points {1,6,9,10} automorphism005
    automorphism005_hole automorphism005_root (by decide +kernel) (rep002 halph)

theorem query279 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,7,9,11} :=
  obstruction_transport link52 FastDual52_002.points {1,7,9,11} automorphism006
    automorphism006_hole automorphism006_root (by decide +kernel) (rep002 halph)

theorem query302 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,3,6,11} :=
  obstruction_transport link52 FastDual52_002.points {2,3,6,11} automorphism016
    automorphism016_hole automorphism016_root (by decide +kernel) (rep002 halph)

theorem query305 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,3,7,10} :=
  obstruction_transport link52 FastDual52_002.points {2,3,7,10} automorphism015
    automorphism015_hole automorphism015_root (by decide +kernel) (rep002 halph)

theorem query336 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,5,6,9} :=
  obstruction_transport link52 FastDual52_002.points {2,5,6,9} automorphism011
    automorphism011_hole automorphism011_root (by decide +kernel) (rep002 halph)

theorem query346 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,5,9,10} :=
  obstruction_transport link52 FastDual52_002.points {2,5,9,10} automorphism013
    automorphism013_hole automorphism013_root (by decide +kernel) (rep002 halph)

theorem query352 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,6,7,11} :=
  obstruction_transport link52 FastDual52_002.points {2,6,7,11} automorphism021
    automorphism021_hole automorphism021_root (by decide +kernel) (rep002 halph)

theorem query364 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,7,10,11} :=
  obstruction_transport link52 FastDual52_002.points {2,7,10,11} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep002 halph)

theorem query396 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,5,7,9} :=
  obstruction_transport link52 FastDual52_002.points {3,5,7,9} automorphism012
    automorphism012_hole automorphism012_root (by decide +kernel) (rep002 halph)

theorem query403 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,5,9,11} :=
  obstruction_transport link52 FastDual52_002.points {3,5,9,11} automorphism014
    automorphism014_hole automorphism014_root (by decide +kernel) (rep002 halph)

theorem query407 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,6,7,10} :=
  obstruction_transport link52 FastDual52_002.points {3,6,7,10} automorphism018
    automorphism018_hole automorphism018_root (by decide +kernel) (rep002 halph)

theorem query414 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,6,10,11} :=
  obstruction_transport link52 FastDual52_002.points {3,6,10,11} automorphism019
    automorphism019_hole automorphism019_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete link52 alphabets) :
    ActualObstruction link52 FastDual52_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link52 rootCodes root_binding alphabets halph nonincident_complete
    FastDual52_003.pointList FastDual52_003.columns FastDual52_003.rows FastDual52_003.bound (by decide +kernel)
    FastDual52_003.column_mask FastDual52_003.checked hc F hF hroot hmin hout

theorem query185 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,2,5,11} := rep003 halph

def automorphism023 : Equiv.Perm Point where
  toFun := ![0,2,1,3,4,6,5,7,8,10,9,11,12]
  invFun := ![0,2,1,3,4,6,5,7,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism023_hole : automorphism023 hole = hole := by decide +kernel

theorem automorphism023_root : transport automorphism023 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism023 (by decide +kernel)

theorem query190 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,2,6,11} :=
  obstruction_transport link52 FastDual52_003.points {1,2,6,11} automorphism023
    automorphism023_hole automorphism023_root (by decide +kernel) (rep003 halph)

theorem query192 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,2,7,9} :=
  obstruction_transport link52 FastDual52_003.points {1,2,7,9} automorphism022
    automorphism022_hole automorphism022_root (by decide +kernel) (rep003 halph)

theorem query193 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,2,7,10} :=
  obstruction_transport link52 FastDual52_003.points {1,2,7,10} automorphism008
    automorphism008_hole automorphism008_root (by decide +kernel) (rep003 halph)

def automorphism024 : Equiv.Perm Point where
  toFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  invFun := ![0,1,3,2,4,5,7,6,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism024_hole : automorphism024 hole = hole := by decide +kernel

theorem automorphism024_root : transport automorphism024 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism024 (by decide +kernel)

theorem query212 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,3,5,10} :=
  obstruction_transport link52 FastDual52_003.points {1,3,5,10} automorphism024
    automorphism024_hole automorphism024_root (by decide +kernel) (rep003 halph)

theorem query216 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,3,6,9} :=
  obstruction_transport link52 FastDual52_003.points {1,3,6,9} automorphism009
    automorphism009_hole automorphism009_root (by decide +kernel) (rep003 halph)

theorem query218 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,3,6,11} :=
  obstruction_transport link52 FastDual52_003.points {1,3,6,11} automorphism010
    automorphism010_hole automorphism010_root (by decide +kernel) (rep003 halph)

def automorphism025 : Equiv.Perm Point where
  toFun := ![0,3,1,2,4,7,5,6,8,11,9,10,12]
  invFun := ![0,2,3,1,4,6,7,5,8,10,11,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism025_hole : automorphism025 hole = hole := by decide +kernel

theorem automorphism025_root : transport automorphism025 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism025 (by decide +kernel)

theorem query221 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,3,7,10} :=
  obstruction_transport link52 FastDual52_003.points {1,3,7,10} automorphism025
    automorphism025_hole automorphism025_root (by decide +kernel) (rep003 halph)

def automorphism026 : Equiv.Perm Point where
  toFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  invFun := ![4,5,6,7,0,1,2,3,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism026_hole : automorphism026 hole = hole := by decide +kernel

theorem automorphism026_root : transport automorphism026 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism026 (by decide +kernel)

theorem query254 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,5,6,11} :=
  obstruction_transport link52 FastDual52_003.points {1,5,6,11} automorphism026
    automorphism026_hole automorphism026_root (by decide +kernel) (rep003 halph)

def automorphism027 : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  invFun := ![4,5,7,6,0,1,3,2,8,9,11,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism027_hole : automorphism027 hole = hole := by decide +kernel

theorem automorphism027_root : transport automorphism027 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism027 (by decide +kernel)

theorem query257 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,5,7,10} :=
  obstruction_transport link52 FastDual52_003.points {1,5,7,10} automorphism027
    automorphism027_hole automorphism027_root (by decide +kernel) (rep003 halph)

theorem query267 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,6,7,10} :=
  obstruction_transport link52 FastDual52_003.points {1,6,7,10} automorphism018
    automorphism018_hole automorphism018_root (by decide +kernel) (rep003 halph)

theorem query268 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,6,7,11} :=
  obstruction_transport link52 FastDual52_003.points {1,6,7,11} automorphism021
    automorphism021_hole automorphism021_root (by decide +kernel) (rep003 halph)

def automorphism028 : Equiv.Perm Point where
  toFun := ![8,9,11,10,0,1,3,2,4,5,7,6,12]
  invFun := ![4,5,7,6,8,9,11,10,0,1,3,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism028_hole : automorphism028 hole = hole := by decide +kernel

theorem automorphism028_root : transport automorphism028 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism028 (by decide +kernel)

theorem query273 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,6,9,11} :=
  obstruction_transport link52 FastDual52_003.points {1,6,9,11} automorphism028
    automorphism028_hole automorphism028_root (by decide +kernel) (rep003 halph)

theorem query274 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,6,10,11} :=
  obstruction_transport link52 FastDual52_003.points {1,6,10,11} automorphism019
    automorphism019_hole automorphism019_root (by decide +kernel) (rep003 halph)

def automorphism029 : Equiv.Perm Point where
  toFun := ![8,9,10,11,0,1,2,3,4,5,6,7,12]
  invFun := ![4,5,6,7,8,9,10,11,0,1,2,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism029_hole : automorphism029 hole = hole := by decide +kernel

theorem automorphism029_root : transport automorphism029 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism029 (by decide +kernel)

theorem query278 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,7,9,10} :=
  obstruction_transport link52 FastDual52_003.points {1,7,9,10} automorphism029
    automorphism029_hole automorphism029_root (by decide +kernel) (rep003 halph)

theorem query280 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,7,10,11} :=
  obstruction_transport link52 FastDual52_003.points {1,7,10,11} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep003 halph)

theorem query296 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,3,5,10} :=
  obstruction_transport link52 FastDual52_003.points {2,3,5,10} automorphism015
    automorphism015_hole automorphism015_root (by decide +kernel) (rep003 halph)

theorem query297 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,3,5,11} :=
  obstruction_transport link52 FastDual52_003.points {2,3,5,11} automorphism016
    automorphism016_hole automorphism016_root (by decide +kernel) (rep003 halph)

def automorphism030 : Equiv.Perm Point where
  toFun := ![0,2,3,1,4,6,7,5,8,10,11,9,12]
  invFun := ![0,3,1,2,4,7,5,6,8,11,9,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism030_hole : automorphism030 hole = hole := by decide +kernel

theorem automorphism030_root : transport automorphism030 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism030 (by decide +kernel)

theorem query300 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,3,6,9} :=
  obstruction_transport link52 FastDual52_003.points {2,3,6,9} automorphism030
    automorphism030_hole automorphism030_root (by decide +kernel) (rep003 halph)

def automorphism031 : Equiv.Perm Point where
  toFun := ![0,3,2,1,4,7,6,5,8,11,10,9,12]
  invFun := ![0,3,2,1,4,7,6,5,8,11,10,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism031_hole : automorphism031 hole = hole := by decide +kernel

theorem automorphism031_root : transport automorphism031 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism031 (by decide +kernel)

theorem query304 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,3,7,9} :=
  obstruction_transport link52 FastDual52_003.points {2,3,7,9} automorphism031
    automorphism031_hole automorphism031_root (by decide +kernel) (rep003 halph)

def automorphism032 : Equiv.Perm Point where
  toFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  invFun := ![4,6,5,7,0,2,1,3,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism032_hole : automorphism032 hole = hole := by decide +kernel

theorem automorphism032_root : transport automorphism032 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism032 (by decide +kernel)

theorem query338 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,5,6,11} :=
  obstruction_transport link52 FastDual52_003.points {2,5,6,11} automorphism032
    automorphism032_hole automorphism032_root (by decide +kernel) (rep003 halph)

theorem query340 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,5,7,9} :=
  obstruction_transport link52 FastDual52_003.points {2,5,7,9} automorphism012
    automorphism012_hole automorphism012_root (by decide +kernel) (rep003 halph)

theorem query342 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,5,7,11} :=
  obstruction_transport link52 FastDual52_003.points {2,5,7,11} automorphism020
    automorphism020_hole automorphism020_root (by decide +kernel) (rep003 halph)

theorem query347 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,5,9,11} :=
  obstruction_transport link52 FastDual52_003.points {2,5,9,11} automorphism014
    automorphism014_hole automorphism014_root (by decide +kernel) (rep003 halph)

def automorphism033 : Equiv.Perm Point where
  toFun := ![8,10,11,9,0,2,3,1,4,6,7,5,12]
  invFun := ![4,7,5,6,8,11,9,10,0,3,1,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism033_hole : automorphism033 hole = hole := by decide +kernel

theorem automorphism033_root : transport automorphism033 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism033 (by decide +kernel)

theorem query348 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,5,10,11} :=
  obstruction_transport link52 FastDual52_003.points {2,5,10,11} automorphism033
    automorphism033_hole automorphism033_root (by decide +kernel) (rep003 halph)

def automorphism034 : Equiv.Perm Point where
  toFun := ![4,6,7,5,0,2,3,1,8,10,11,9,12]
  invFun := ![4,7,5,6,0,3,1,2,8,11,9,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism034_hole : automorphism034 hole = hole := by decide +kernel

theorem automorphism034_root : transport automorphism034 link52 = link52 :=
  root_symmetry_of_codes rootCodes link52 root_binding automorphism034 (by decide +kernel)

theorem query350 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,6,7,9} :=
  obstruction_transport link52 FastDual52_003.points {2,6,7,9} automorphism034
    automorphism034_hole automorphism034_root (by decide +kernel) (rep003 halph)

theorem query362 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,7,9,10} :=
  obstruction_transport link52 FastDual52_003.points {2,7,9,10} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem query363 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,7,9,11} :=
  obstruction_transport link52 FastDual52_003.points {2,7,9,11} automorphism006
    automorphism006_hole automorphism006_root (by decide +kernel) (rep003 halph)

theorem query392 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,5,6,9} :=
  obstruction_transport link52 FastDual52_003.points {3,5,6,9} automorphism011
    automorphism011_hole automorphism011_root (by decide +kernel) (rep003 halph)

theorem query393 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,5,6,10} :=
  obstruction_transport link52 FastDual52_003.points {3,5,6,10} automorphism017
    automorphism017_hole automorphism017_root (by decide +kernel) (rep003 halph)

theorem query397 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,5,7,10} :=
  obstruction_transport link52 FastDual52_003.points {3,5,7,10} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep003 halph)

theorem query402 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,5,9,10} :=
  obstruction_transport link52 FastDual52_003.points {3,5,9,10} automorphism013
    automorphism013_hole automorphism013_root (by decide +kernel) (rep003 halph)

theorem query404 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,5,10,11} :=
  obstruction_transport link52 FastDual52_003.points {3,5,10,11} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep003 halph)

theorem query406 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,6,7,9} :=
  obstruction_transport link52 FastDual52_003.points {3,6,7,9} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep003 halph)

theorem query412 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,6,9,10} :=
  obstruction_transport link52 FastDual52_003.points {3,6,9,10} automorphism005
    automorphism005_hole automorphism005_root (by decide +kernel) (rep003 halph)

theorem query413 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,6,9,11} :=
  obstruction_transport link52 FastDual52_003.points {3,6,9,11} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete link52 alphabets) :
    ActualObstruction link52 FastDual52_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction link52 rootCodes root_binding alphabets halph nonincident_complete
    FastDual52_004.pointList FastDual52_004.columns FastDual52_004.rows FastDual52_004.bound (by decide +kernel)
    FastDual52_004.column_mask FastDual52_004.checked hc F hF hroot hmin hout

theorem query194 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,2,7,11} := rep004 halph

theorem query217 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,3,6,10} :=
  obstruction_transport link52 FastDual52_004.points {1,3,6,10} automorphism010
    automorphism010_hole automorphism010_root (by decide +kernel) (rep004 halph)

theorem query264 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,5,10,11} :=
  obstruction_transport link52 FastDual52_004.points {1,5,10,11} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep004 halph)

theorem query266 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {1,6,7,9} :=
  obstruction_transport link52 FastDual52_004.points {1,6,7,9} automorphism021
    automorphism021_hole automorphism021_root (by decide +kernel) (rep004 halph)

theorem query295 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,3,5,9} :=
  obstruction_transport link52 FastDual52_004.points {2,3,5,9} automorphism016
    automorphism016_hole automorphism016_root (by decide +kernel) (rep004 halph)

theorem query341 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,5,7,10} :=
  obstruction_transport link52 FastDual52_004.points {2,5,7,10} automorphism020
    automorphism020_hole automorphism020_root (by decide +kernel) (rep004 halph)

theorem query357 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {2,6,9,11} :=
  obstruction_transport link52 FastDual52_004.points {2,6,9,11} automorphism006
    automorphism006_hole automorphism006_root (by decide +kernel) (rep004 halph)

theorem query394 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,5,6,11} :=
  obstruction_transport link52 FastDual52_004.points {3,5,6,11} automorphism017
    automorphism017_hole automorphism017_root (by decide +kernel) (rep004 halph)

theorem query418 (halph : AlphabetComplete link52 alphabets) : ActualObstruction link52 {3,7,9,10} :=
  obstruction_transport link52 FastDual52_004.points {3,7,9,10} automorphism005
    automorphism005_hole automorphism005_root (by decide +kernel) (rep004 halph)

def dualQuads : List (Finset Point) := [{1,2,5,6},{1,2,9,10},{1,3,5,7},{1,3,9,11},{2,3,6,7},{2,3,10,11},{5,6,9,10},{5,7,9,11},{6,7,10,11},{1,2,5,9},{1,2,6,10},{1,3,5,9},{1,3,7,11},{1,5,6,9},{1,5,7,9},{1,5,9,10},{1,5,9,11},{2,3,6,10},{2,3,7,11},{2,5,6,10},{2,6,7,10},{2,6,9,10},{2,6,10,11},{3,5,7,11},{3,6,7,11},{3,7,9,11},{3,7,10,11},{1,2,5,10},{1,2,6,9},{1,3,5,11},{1,3,7,9},{1,5,6,10},{1,5,7,11},{1,6,9,10},{1,7,9,11},{2,3,6,11},{2,3,7,10},{2,5,6,9},{2,5,9,10},{2,6,7,11},{2,7,10,11},{3,5,7,9},{3,5,9,11},{3,6,7,10},{3,6,10,11},{1,2,5,11},{1,2,6,11},{1,2,7,9},{1,2,7,10},{1,3,5,10},{1,3,6,9},{1,3,6,11},{1,3,7,10},{1,5,6,11},{1,5,7,10},{1,6,7,10},{1,6,7,11},{1,6,9,11},{1,6,10,11},{1,7,9,10},{1,7,10,11},{2,3,5,10},{2,3,5,11},{2,3,6,9},{2,3,7,9},{2,5,6,11},{2,5,7,9},{2,5,7,11},{2,5,9,11},{2,5,10,11},{2,6,7,9},{2,7,9,10},{2,7,9,11},{3,5,6,9},{3,5,6,10},{3,5,7,10},{3,5,9,10},{3,5,10,11},{3,6,7,9},{3,6,9,10},{3,6,9,11},{1,2,7,11},{1,3,6,10},{1,5,10,11},{1,6,7,9},{2,3,5,9},{2,5,7,10},{2,6,9,11},{3,5,6,11},{3,7,9,10}]

theorem dual_actual (halph : AlphabetComplete link52 alphabets)
    (Q : Finset Point) (hQ : Q ∈ dualQuads) : ActualObstruction link52 Q := by
  simp only [dualQuads,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact query180 halph
  · exact query198 halph
  · exact query209 halph
  · exact query227 halph
  · exact query298 halph
  · exact query312 halph
  · exact query467 halph
  · exact query474 halph
  · exact query485 halph
  · exact query183 halph
  · exact query189 halph
  · exact query211 halph
  · exact query222 halph
  · exact query252 halph
  · exact query256 halph
  · exact query262 halph
  · exact query263 halph
  · exact query301 halph
  · exact query306 halph
  · exact query337 halph
  · exact query351 halph
  · exact query356 halph
  · exact query358 halph
  · exact query398 halph
  · exact query408 halph
  · exact query419 halph
  · exact query420 halph
  · exact query184 halph
  · exact query188 halph
  · exact query213 halph
  · exact query220 halph
  · exact query253 halph
  · exact query258 halph
  · exact query272 halph
  · exact query279 halph
  · exact query302 halph
  · exact query305 halph
  · exact query336 halph
  · exact query346 halph
  · exact query352 halph
  · exact query364 halph
  · exact query396 halph
  · exact query403 halph
  · exact query407 halph
  · exact query414 halph
  · exact query185 halph
  · exact query190 halph
  · exact query192 halph
  · exact query193 halph
  · exact query212 halph
  · exact query216 halph
  · exact query218 halph
  · exact query221 halph
  · exact query254 halph
  · exact query257 halph
  · exact query267 halph
  · exact query268 halph
  · exact query273 halph
  · exact query274 halph
  · exact query278 halph
  · exact query280 halph
  · exact query296 halph
  · exact query297 halph
  · exact query300 halph
  · exact query304 halph
  · exact query338 halph
  · exact query340 halph
  · exact query342 halph
  · exact query347 halph
  · exact query348 halph
  · exact query350 halph
  · exact query362 halph
  · exact query363 halph
  · exact query392 halph
  · exact query393 halph
  · exact query397 halph
  · exact query402 halph
  · exact query404 halph
  · exact query406 halph
  · exact query412 halph
  · exact query413 halph
  · exact query194 halph
  · exact query217 halph
  · exact query264 halph
  · exact query266 halph
  · exact query295 halph
  · exact query341 halph
  · exact query357 halph
  · exact query394 halph
  · exact query418 halph

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel

theorem all_foursets (halph : AlphabetComplete link52 alphabets)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction link52 Q :=
  class_census link52 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph) coverage_checked Q hQ
end C13.Global.Relative.Source52
