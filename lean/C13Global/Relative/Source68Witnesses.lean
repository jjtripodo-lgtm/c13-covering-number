import C13Global.CensusCore
import C13Global.FastDualBridge
import C13Global.CodedSymmetry
import C13Global.Data.Source68
import C13Global.FastGroups.Source68Part00
namespace C13.Global.Relative.Source68
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source68
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = figure6 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets :=
  nonincident_complete_of_check alphabets nonincident_checked

theorem empty_points_checked : emptyCases.all (fun c => c.1.all (fun q => decide (q ≠ hole))) = true := by decide +kernel

theorem empty_actual (halph : AlphabetComplete figure6 alphabets)
    (c : EmptyCase) (hc : c ∈ emptyCases) : ActualObstruction figure6 c.1.toFinset := by
  intro hclass F hcover hroot hmin hout
  apply empty_actual_obstruction figure6 rootCodes root_binding alphabets halph
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc) hclass F hcover hroot
  · intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp empty_points_checked c hc) q hq)
  · intro q hq
    exact hmin q (List.mem_toFinset.mpr hq)

theorem rep000 (halph : AlphabetComplete figure6 alphabets) :
    ActualObstruction figure6 FastDual68_000.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction figure6 rootCodes root_binding alphabets halph nonincident_complete
    FastDual68_000.pointList FastDual68_000.columns FastDual68_000.rows FastDual68_000.bound (by decide +kernel)
    FastDual68_000.column_mask FastDual68_000.checked hc F hF hroot hmin hout

theorem query000 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,2,3} := rep000 halph

def automorphism000 : Equiv.Perm Point where
  toFun := ![9,6,3,0,5,4,8,11,1,7,10,2,12]
  invFun := ![3,8,11,2,5,4,1,9,6,0,10,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism000_hole : automorphism000 hole = hole := by decide +kernel

theorem automorphism000_root : transport automorphism000 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism000 (by decide +kernel)

theorem query096 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,3,6,9} :=
  obstruction_transport figure6 FastDual68_000.points {0,3,6,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep000 halph)

def automorphism001 : Equiv.Perm Point where
  toFun := ![11,10,0,6,5,4,7,8,3,2,1,9,12]
  invFun := ![2,10,9,8,5,4,3,6,7,11,1,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism001_hole : automorphism001 hole = hole := by decide +kernel

theorem automorphism001_root : transport automorphism001 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism001 (by decide +kernel)

theorem query154 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,6,10,11} :=
  obstruction_transport figure6 FastDual68_000.points {0,6,10,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep000 halph)

def automorphism002 : Equiv.Perm Point where
  toFun := ![8,7,0,9,5,4,10,11,3,2,1,6,12]
  invFun := ![2,10,9,8,5,4,11,1,0,3,6,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism002_hole : automorphism002 hole = hole := by decide +kernel

theorem automorphism002_root : transport automorphism002 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism002 (by decide +kernel)

theorem query155 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,7,8,9} :=
  obstruction_transport figure6 FastDual68_000.points {0,7,8,9} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep000 halph)

def automorphism003 : Equiv.Perm Point where
  toFun := ![10,7,3,1,5,4,8,11,0,6,9,2,12]
  invFun := ![8,3,11,2,5,4,9,1,6,10,0,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism003_hole : automorphism003 hole = hole := by decide +kernel

theorem automorphism003_root : transport automorphism003 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism003 (by decide +kernel)

theorem query221 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,3,7,10} :=
  obstruction_transport figure6 FastDual68_000.points {1,3,7,10} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep000 halph)

def automorphism004 : Equiv.Perm Point where
  toFun := ![8,6,1,10,5,4,9,11,3,2,0,7,12]
  invFun := ![10,2,9,8,5,4,1,11,0,6,3,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism004_hole : automorphism004 hole = hole := by decide +kernel

theorem automorphism004_root : transport automorphism004 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism004 (by decide +kernel)

theorem query270 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,6,8,10} :=
  obstruction_transport figure6 FastDual68_000.points {1,6,8,10} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep000 halph)

def automorphism005 : Equiv.Perm Point where
  toFun := ![11,9,1,7,5,4,6,8,3,2,0,10,12]
  invFun := ![10,2,9,8,5,4,6,3,7,1,11,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism005_hole : automorphism005 hole = hole := by decide +kernel

theorem automorphism005_root : transport automorphism005 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism005 (by decide +kernel)

theorem query279 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,7,9,11} :=
  obstruction_transport figure6 FastDual68_000.points {1,7,9,11} automorphism005
    automorphism005_hole automorphism005_root (by decide +kernel) (rep000 halph)

def automorphism006 : Equiv.Perm Point where
  toFun := ![11,8,3,2,5,4,7,10,0,6,9,1,12]
  invFun := ![8,11,3,2,5,4,9,6,1,10,7,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism006_hole : automorphism006 hole = hole := by decide +kernel

theorem automorphism006_root : transport automorphism006 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism006 (by decide +kernel)

theorem query309 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,3,8,11} :=
  obstruction_transport figure6 FastDual68_000.points {2,3,8,11} automorphism006
    automorphism006_hole automorphism006_root (by decide +kernel) (rep000 halph)

def automorphism007 : Equiv.Perm Point where
  toFun := ![7,6,2,11,5,4,9,10,3,1,0,8,12]
  invFun := ![10,9,2,8,5,4,1,0,11,6,7,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism007_hole : automorphism007 hole = hole := by decide +kernel

theorem automorphism007_root : transport automorphism007 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism007 (by decide +kernel)

theorem query352 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,6,7,11} :=
  obstruction_transport figure6 FastDual68_000.points {2,6,7,11} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep000 halph)

def automorphism008 : Equiv.Perm Point where
  toFun := ![10,9,2,8,5,4,6,7,3,1,0,11,12]
  invFun := ![10,9,2,8,5,4,6,7,3,1,0,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism008_hole : automorphism008 hole = hole := by decide +kernel

theorem automorphism008_root : transport automorphism008 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism008 (by decide +kernel)

theorem query365 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,8,9,10} :=
  obstruction_transport figure6 FastDual68_000.points {2,8,9,10} automorphism008
    automorphism008_hole automorphism008_root (by decide +kernel) (rep000 halph)

theorem rep001 (halph : AlphabetComplete figure6 alphabets) :
    ActualObstruction figure6 FastDual68_001.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction figure6 rootCodes root_binding alphabets halph nonincident_complete
    FastDual68_001.pointList FastDual68_001.columns FastDual68_001.rows FastDual68_001.bound (by decide +kernel)
    FastDual68_001.column_mask FastDual68_001.checked hc F hF hroot hmin hout

theorem query003 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,2,6} := rep001 halph

def automorphism009 : Equiv.Perm Point where
  toFun := ![1,2,0,3,5,4,7,8,6,10,11,9,12]
  invFun := ![2,0,1,3,5,4,8,6,7,11,9,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism009_hole : automorphism009 hole = hole := by decide +kernel

theorem automorphism009_root : transport automorphism009 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism009 (by decide +kernel)

theorem query004 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,2,7} :=
  obstruction_transport figure6 FastDual68_001.points {0,1,2,7} automorphism009
    automorphism009_hole automorphism009_root (by decide +kernel) (rep001 halph)

def automorphism010 : Equiv.Perm Point where
  toFun := ![2,1,0,3,5,4,8,7,6,11,10,9,12]
  invFun := ![2,1,0,3,5,4,8,7,6,11,10,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism010_hole : automorphism010 hole = hole := by decide +kernel

theorem automorphism010_root : transport automorphism010 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism010 (by decide +kernel)

theorem query005 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,2,8} :=
  obstruction_transport figure6 FastDual68_001.points {0,1,2,8} automorphism010
    automorphism010_hole automorphism010_root (by decide +kernel) (rep001 halph)

def automorphism011 : Equiv.Perm Point where
  toFun := ![0,2,1,3,5,4,9,11,10,6,8,7,12]
  invFun := ![0,2,1,3,5,4,9,11,10,6,8,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism011_hole : automorphism011 hole = hole := by decide +kernel

theorem automorphism011_root : transport automorphism011 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism011 (by decide +kernel)

theorem query006 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,2,9} :=
  obstruction_transport figure6 FastDual68_001.points {0,1,2,9} automorphism011
    automorphism011_hole automorphism011_root (by decide +kernel) (rep001 halph)

def automorphism012 : Equiv.Perm Point where
  toFun := ![1,2,0,3,5,4,10,11,9,7,8,6,12]
  invFun := ![2,0,1,3,5,4,11,9,10,8,6,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism012_hole : automorphism012 hole = hole := by decide +kernel

theorem automorphism012_root : transport automorphism012 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism012 (by decide +kernel)

theorem query007 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,2,10} :=
  obstruction_transport figure6 FastDual68_001.points {0,1,2,10} automorphism012
    automorphism012_hole automorphism012_root (by decide +kernel) (rep001 halph)

def automorphism013 : Equiv.Perm Point where
  toFun := ![2,1,0,3,5,4,11,10,9,8,7,6,12]
  invFun := ![2,1,0,3,5,4,11,10,9,8,7,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism013_hole : automorphism013 hole = hole := by decide +kernel

theorem automorphism013_root : transport automorphism013 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism013 (by decide +kernel)

theorem query008 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,2,11} :=
  obstruction_transport figure6 FastDual68_001.points {0,1,2,11} automorphism013
    automorphism013_hole automorphism013_root (by decide +kernel) (rep001 halph)

def automorphism014 : Equiv.Perm Point where
  toFun := ![6,8,1,10,5,4,0,2,7,11,9,3,12]
  invFun := ![6,2,7,11,5,4,0,8,1,10,3,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism014_hole : automorphism014 hole = hole := by decide +kernel

theorem automorphism014_root : transport automorphism014 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism014 (by decide +kernel)

theorem query031 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,6,8} :=
  obstruction_transport figure6 FastDual68_001.points {0,1,6,8} automorphism014
    automorphism014_hole automorphism014_root (by decide +kernel) (rep001 halph)

def automorphism015 : Equiv.Perm Point where
  toFun := ![7,8,0,9,5,4,1,2,6,11,10,3,12]
  invFun := ![2,6,7,11,5,4,8,0,1,3,10,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism015_hole : automorphism015 hole = hole := by decide +kernel

theorem automorphism015_root : transport automorphism015 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism015 (by decide +kernel)

theorem query035 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,7,8} :=
  obstruction_transport figure6 FastDual68_001.points {0,1,7,8} automorphism015
    automorphism015_hole automorphism015_root (by decide +kernel) (rep001 halph)

def automorphism016 : Equiv.Perm Point where
  toFun := ![9,11,1,7,5,4,0,2,10,8,6,3,12]
  invFun := ![6,2,7,11,5,4,10,3,9,0,8,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism016_hole : automorphism016 hole = hole := by decide +kernel

theorem automorphism016_root : transport automorphism016 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism016 (by decide +kernel)

theorem query043 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,9,11} :=
  obstruction_transport figure6 FastDual68_001.points {0,1,9,11} automorphism016
    automorphism016_hole automorphism016_root (by decide +kernel) (rep001 halph)

def automorphism017 : Equiv.Perm Point where
  toFun := ![10,11,0,6,5,4,1,2,9,8,7,3,12]
  invFun := ![2,6,7,11,5,4,3,10,9,8,0,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism017_hole : automorphism017 hole = hole := by decide +kernel

theorem automorphism017_root : transport automorphism017 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism017 (by decide +kernel)

theorem query044 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,10,11} :=
  obstruction_transport figure6 FastDual68_001.points {0,1,10,11} automorphism017
    automorphism017_hole automorphism017_root (by decide +kernel) (rep001 halph)

def automorphism018 : Equiv.Perm Point where
  toFun := ![6,7,2,11,5,4,0,1,8,10,9,3,12]
  invFun := ![6,7,2,11,5,4,0,1,8,10,9,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism018_hole : automorphism018 hole = hole := by decide +kernel

theorem automorphism018_root : transport automorphism018 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism018 (by decide +kernel)

theorem query066 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,6,7} :=
  obstruction_transport figure6 FastDual68_001.points {0,2,6,7} automorphism018
    automorphism018_hole automorphism018_root (by decide +kernel) (rep001 halph)

def automorphism019 : Equiv.Perm Point where
  toFun := ![8,7,0,9,5,4,2,1,6,10,11,3,12]
  invFun := ![2,7,6,11,5,4,8,1,0,3,9,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism019_hole : automorphism019 hole = hole := by decide +kernel

theorem automorphism019_root : transport automorphism019 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism019 (by decide +kernel)

theorem query071 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,7,8} :=
  obstruction_transport figure6 FastDual68_001.points {0,2,7,8} automorphism019
    automorphism019_hole automorphism019_root (by decide +kernel) (rep001 halph)

def automorphism020 : Equiv.Perm Point where
  toFun := ![9,10,2,8,5,4,0,1,11,7,6,3,12]
  invFun := ![6,7,2,11,5,4,10,9,3,0,1,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism020_hole : automorphism020 hole = hole := by decide +kernel

theorem automorphism020_root : transport automorphism020 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism020 (by decide +kernel)

theorem query078 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,9,10} :=
  obstruction_transport figure6 FastDual68_001.points {0,2,9,10} automorphism020
    automorphism020_hole automorphism020_root (by decide +kernel) (rep001 halph)

def automorphism021 : Equiv.Perm Point where
  toFun := ![11,10,0,6,5,4,2,1,9,7,8,3,12]
  invFun := ![2,7,6,11,5,4,3,9,10,8,1,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism021_hole : automorphism021 hole = hole := by decide +kernel

theorem automorphism021_root : transport automorphism021 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism021 (by decide +kernel)

theorem query080 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,10,11} :=
  obstruction_transport figure6 FastDual68_001.points {0,2,10,11} automorphism021
    automorphism021_hole automorphism021_root (by decide +kernel) (rep001 halph)

def automorphism022 : Equiv.Perm Point where
  toFun := ![0,8,7,9,5,4,3,10,11,6,2,1,12]
  invFun := ![0,11,10,6,5,4,9,2,1,3,7,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism022_hole : automorphism022 hole = hole := by decide +kernel

theorem automorphism022_root : transport automorphism022 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism022 (by decide +kernel)

theorem query099 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,3,7,8} :=
  obstruction_transport figure6 FastDual68_001.points {0,3,7,8} automorphism022
    automorphism022_hole automorphism022_root (by decide +kernel) (rep001 halph)

def automorphism023 : Equiv.Perm Point where
  toFun := ![3,10,7,1,5,4,0,8,11,2,6,9,12]
  invFun := ![6,3,9,0,5,4,10,2,7,11,1,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism023_hole : automorphism023 hole = hole := by decide +kernel

theorem automorphism023_root : transport automorphism023 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism023 (by decide +kernel)

theorem query101 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,3,7,10} :=
  obstruction_transport figure6 FastDual68_001.points {0,3,7,10} automorphism023
    automorphism023_hole automorphism023_root (by decide +kernel) (rep001 halph)

def automorphism024 : Equiv.Perm Point where
  toFun := ![3,11,8,2,5,4,0,7,10,1,6,9,12]
  invFun := ![6,9,3,0,5,4,10,7,2,11,8,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism024_hole : automorphism024 hole = hole := by decide +kernel

theorem automorphism024_root : transport automorphism024 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism024 (by decide +kernel)

theorem query105 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,3,8,11} :=
  obstruction_transport figure6 FastDual68_001.points {0,3,8,11} automorphism024
    automorphism024_hole automorphism024_root (by decide +kernel) (rep001 halph)

def automorphism025 : Equiv.Perm Point where
  toFun := ![0,11,10,6,5,4,3,7,8,9,2,1,12]
  invFun := ![0,11,10,6,5,4,3,7,8,9,2,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism025_hole : automorphism025 hole = hole := by decide +kernel

theorem automorphism025_root : transport automorphism025 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism025 (by decide +kernel)

theorem query108 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,3,10,11} :=
  obstruction_transport figure6 FastDual68_001.points {0,3,10,11} automorphism025
    automorphism025_hole automorphism025_root (by decide +kernel) (rep001 halph)

def automorphism026 : Equiv.Perm Point where
  toFun := ![0,8,7,9,5,4,6,2,1,3,10,11,12]
  invFun := ![0,8,7,9,5,4,6,2,1,3,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism026_hole : automorphism026 hole = hole := by decide +kernel

theorem automorphism026_root : transport automorphism026 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism026 (by decide +kernel)

theorem query145 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,6,7,8} :=
  obstruction_transport figure6 FastDual68_001.points {0,6,7,8} automorphism026
    automorphism026_hole automorphism026_root (by decide +kernel) (rep001 halph)

theorem query156 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,7,8,10} :=
  obstruction_transport figure6 FastDual68_001.points {0,7,8,10} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep001 halph)

def automorphism027 : Equiv.Perm Point where
  toFun := ![7,8,0,9,5,4,11,10,3,1,2,6,12]
  invFun := ![2,9,10,8,5,4,11,0,1,3,7,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism027_hole : automorphism027 hole = hole := by decide +kernel

theorem automorphism027_root : transport automorphism027 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism027 (by decide +kernel)

theorem query157 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,7,8,11} :=
  obstruction_transport figure6 FastDual68_001.points {0,7,8,11} automorphism027
    automorphism027_hole automorphism027_root (by decide +kernel) (rep001 halph)

theorem query160 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,7,10,11} :=
  obstruction_transport figure6 FastDual68_001.points {0,7,10,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep001 halph)

def automorphism028 : Equiv.Perm Point where
  toFun := ![10,11,0,6,5,4,8,7,3,1,2,9,12]
  invFun := ![2,9,10,8,5,4,3,7,6,11,0,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism028_hole : automorphism028 hole = hole := by decide +kernel

theorem automorphism028_root : transport automorphism028 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism028 (by decide +kernel)

theorem query163 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,8,10,11} :=
  obstruction_transport figure6 FastDual68_001.points {0,8,10,11} automorphism028
    automorphism028_hole automorphism028_root (by decide +kernel) (rep001 halph)

def automorphism029 : Equiv.Perm Point where
  toFun := ![0,11,10,6,5,4,9,2,1,3,7,8,12]
  invFun := ![0,8,7,9,5,4,3,10,11,6,2,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism029_hole : automorphism029 hole = hole := by decide +kernel

theorem automorphism029_root : transport automorphism029 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism029 (by decide +kernel)

theorem query164 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,9,10,11} :=
  obstruction_transport figure6 FastDual68_001.points {0,9,10,11} automorphism029
    automorphism029_hole automorphism029_root (by decide +kernel) (rep001 halph)

def automorphism030 : Equiv.Perm Point where
  toFun := ![7,6,2,11,5,4,1,0,8,9,10,3,12]
  invFun := ![7,6,2,11,5,4,1,0,8,9,10,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism030_hole : automorphism030 hole = hole := by decide +kernel

theorem automorphism030_root : transport automorphism030 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism030 (by decide +kernel)

theorem query186 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,6,7} :=
  obstruction_transport figure6 FastDual68_001.points {1,2,6,7} automorphism030
    automorphism030_hole automorphism030_root (by decide +kernel) (rep001 halph)

def automorphism031 : Equiv.Perm Point where
  toFun := ![8,6,1,10,5,4,2,0,7,9,11,3,12]
  invFun := ![7,2,6,11,5,4,1,8,0,9,3,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism031_hole : automorphism031 hole = hole := by decide +kernel

theorem automorphism031_root : transport automorphism031 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism031 (by decide +kernel)

theorem query187 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,6,8} :=
  obstruction_transport figure6 FastDual68_001.points {1,2,6,8} automorphism031
    automorphism031_hole automorphism031_root (by decide +kernel) (rep001 halph)

def automorphism032 : Equiv.Perm Point where
  toFun := ![10,9,2,8,5,4,1,0,11,6,7,3,12]
  invFun := ![7,6,2,11,5,4,9,10,3,1,0,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism032_hole : automorphism032 hole = hole := by decide +kernel

theorem automorphism032_root : transport automorphism032 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism032 (by decide +kernel)

theorem query198 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,9,10} :=
  obstruction_transport figure6 FastDual68_001.points {1,2,9,10} automorphism032
    automorphism032_hole automorphism032_root (by decide +kernel) (rep001 halph)

def automorphism033 : Equiv.Perm Point where
  toFun := ![11,9,1,7,5,4,2,0,10,6,8,3,12]
  invFun := ![7,2,6,11,5,4,9,3,10,1,8,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism033_hole : automorphism033 hole = hole := by decide +kernel

theorem automorphism033_root : transport automorphism033 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism033 (by decide +kernel)

theorem query199 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,9,11} :=
  obstruction_transport figure6 FastDual68_001.points {1,2,9,11} automorphism033
    automorphism033_hole automorphism033_root (by decide +kernel) (rep001 halph)

def automorphism034 : Equiv.Perm Point where
  toFun := ![1,8,6,10,5,4,3,9,11,7,2,0,12]
  invFun := ![11,0,10,6,5,4,2,9,1,7,3,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism034_hole : automorphism034 hole = hole := by decide +kernel

theorem automorphism034_root : transport automorphism034 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism034 (by decide +kernel)

theorem query215 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,3,6,8} :=
  obstruction_transport figure6 FastDual68_001.points {1,3,6,8} automorphism034
    automorphism034_hole automorphism034_root (by decide +kernel) (rep001 halph)

def automorphism035 : Equiv.Perm Point where
  toFun := ![3,9,6,0,5,4,1,8,11,2,7,10,12]
  invFun := ![3,6,9,0,5,4,2,10,7,1,11,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism035_hole : automorphism035 hole = hole := by decide +kernel

theorem automorphism035_root : transport automorphism035 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism035 (by decide +kernel)

theorem query216 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,3,6,9} :=
  obstruction_transport figure6 FastDual68_001.points {1,3,6,9} automorphism035
    automorphism035_hole automorphism035_root (by decide +kernel) (rep001 halph)

def automorphism036 : Equiv.Perm Point where
  toFun := ![3,11,8,2,5,4,1,6,9,0,7,10,12]
  invFun := ![9,6,3,0,5,4,7,10,2,8,11,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism036_hole : automorphism036 hole = hole := by decide +kernel

theorem automorphism036_root : transport automorphism036 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism036 (by decide +kernel)

theorem query225 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,3,8,11} :=
  obstruction_transport figure6 FastDual68_001.points {1,3,8,11} automorphism036
    automorphism036_hole automorphism036_root (by decide +kernel) (rep001 halph)

def automorphism037 : Equiv.Perm Point where
  toFun := ![1,11,9,7,5,4,3,6,8,10,2,0,12]
  invFun := ![11,0,10,6,5,4,7,3,8,2,9,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism037_hole : automorphism037 hole = hole := by decide +kernel

theorem automorphism037_root : transport automorphism037 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism037 (by decide +kernel)

theorem query227 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,3,9,11} :=
  obstruction_transport figure6 FastDual68_001.points {1,3,9,11} automorphism037
    automorphism037_hole automorphism037_root (by decide +kernel) (rep001 halph)

def automorphism038 : Equiv.Perm Point where
  toFun := ![1,8,6,10,5,4,7,2,0,3,9,11,12]
  invFun := ![8,0,7,9,5,4,2,6,1,10,3,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism038_hole : automorphism038 hole = hole := by decide +kernel

theorem automorphism038_root : transport automorphism038 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism038 (by decide +kernel)

theorem query265 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,6,7,8} :=
  obstruction_transport figure6 FastDual68_001.points {1,6,7,8} automorphism038
    automorphism038_hole automorphism038_root (by decide +kernel) (rep001 halph)

theorem query269 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,6,8,9} :=
  obstruction_transport figure6 FastDual68_001.points {1,6,8,9} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep001 halph)

def automorphism039 : Equiv.Perm Point where
  toFun := ![6,8,1,10,5,4,11,9,3,0,2,7,12]
  invFun := ![9,2,10,8,5,4,0,11,1,7,3,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism039_hole : automorphism039 hole = hole := by decide +kernel

theorem automorphism039_root : transport automorphism039 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism039 (by decide +kernel)

theorem query271 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,6,8,11} :=
  obstruction_transport figure6 FastDual68_001.points {1,6,8,11} automorphism039
    automorphism039_hole automorphism039_root (by decide +kernel) (rep001 halph)

theorem query273 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,6,9,11} :=
  obstruction_transport figure6 FastDual68_001.points {1,6,9,11} automorphism005
    automorphism005_hole automorphism005_root (by decide +kernel) (rep001 halph)

def automorphism040 : Equiv.Perm Point where
  toFun := ![9,11,1,7,5,4,8,6,3,0,2,10,12]
  invFun := ![9,2,10,8,5,4,7,3,6,0,11,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism040_hole : automorphism040 hole = hole := by decide +kernel

theorem automorphism040_root : transport automorphism040 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism040 (by decide +kernel)

theorem query282 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,8,9,11} :=
  obstruction_transport figure6 FastDual68_001.points {1,8,9,11} automorphism040
    automorphism040_hole automorphism040_root (by decide +kernel) (rep001 halph)

def automorphism041 : Equiv.Perm Point where
  toFun := ![1,11,9,7,5,4,10,2,0,3,6,8,12]
  invFun := ![8,0,7,9,5,4,10,3,11,2,6,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism041_hole : automorphism041 hole = hole := by decide +kernel

theorem automorphism041_root : transport automorphism041 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism041 (by decide +kernel)

theorem query284 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,9,10,11} :=
  obstruction_transport figure6 FastDual68_001.points {1,9,10,11} automorphism041
    automorphism041_hole automorphism041_root (by decide +kernel) (rep001 halph)

def automorphism042 : Equiv.Perm Point where
  toFun := ![2,7,6,11,5,4,3,9,10,8,1,0,12]
  invFun := ![11,10,0,6,5,4,2,1,9,7,8,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism042_hole : automorphism042 hole = hole := by decide +kernel

theorem automorphism042_root : transport automorphism042 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism042 (by decide +kernel)

theorem query298 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,3,6,7} :=
  obstruction_transport figure6 FastDual68_001.points {2,3,6,7} automorphism042
    automorphism042_hole automorphism042_root (by decide +kernel) (rep001 halph)

def automorphism043 : Equiv.Perm Point where
  toFun := ![3,9,6,0,5,4,2,7,10,1,8,11,12]
  invFun := ![3,9,6,0,5,4,2,7,10,1,8,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism043_hole : automorphism043 hole = hole := by decide +kernel

theorem automorphism043_root : transport automorphism043 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism043 (by decide +kernel)

theorem query300 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,3,6,9} :=
  obstruction_transport figure6 FastDual68_001.points {2,3,6,9} automorphism043
    automorphism043_hole automorphism043_root (by decide +kernel) (rep001 halph)

def automorphism044 : Equiv.Perm Point where
  toFun := ![3,10,7,1,5,4,2,6,9,0,8,11,12]
  invFun := ![9,3,6,0,5,4,7,2,10,8,1,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism044_hole : automorphism044 hole = hole := by decide +kernel

theorem automorphism044_root : transport automorphism044 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism044 (by decide +kernel)

theorem query305 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,3,7,10} :=
  obstruction_transport figure6 FastDual68_001.points {2,3,7,10} automorphism044
    automorphism044_hole automorphism044_root (by decide +kernel) (rep001 halph)

def automorphism045 : Equiv.Perm Point where
  toFun := ![2,10,9,8,5,4,3,6,7,11,1,0,12]
  invFun := ![11,10,0,6,5,4,7,8,3,2,1,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism045_hole : automorphism045 hole = hole := by decide +kernel

theorem automorphism045_root : transport automorphism045 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism045 (by decide +kernel)

theorem query310 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,3,9,10} :=
  obstruction_transport figure6 FastDual68_001.points {2,3,9,10} automorphism045
    automorphism045_hole automorphism045_root (by decide +kernel) (rep001 halph)

def automorphism046 : Equiv.Perm Point where
  toFun := ![2,7,6,11,5,4,8,1,0,3,9,10,12]
  invFun := ![8,7,0,9,5,4,2,1,6,10,11,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism046_hole : automorphism046 hole = hole := by decide +kernel

theorem automorphism046_root : transport automorphism046 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism046 (by decide +kernel)

theorem query349 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,6,7,8} :=
  obstruction_transport figure6 FastDual68_001.points {2,6,7,8} automorphism046
    automorphism046_hole automorphism046_root (by decide +kernel) (rep001 halph)

theorem query350 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,6,7,9} :=
  obstruction_transport figure6 FastDual68_001.points {2,6,7,9} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep001 halph)

def automorphism047 : Equiv.Perm Point where
  toFun := ![6,7,2,11,5,4,10,9,3,0,1,8,12]
  invFun := ![9,10,2,8,5,4,0,1,11,7,6,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism047_hole : automorphism047 hole = hole := by decide +kernel

theorem automorphism047_root : transport automorphism047 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism047 (by decide +kernel)

theorem query351 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,6,7,10} :=
  obstruction_transport figure6 FastDual68_001.points {2,6,7,10} automorphism047
    automorphism047_hole automorphism047_root (by decide +kernel) (rep001 halph)

theorem query356 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,6,9,10} :=
  obstruction_transport figure6 FastDual68_001.points {2,6,9,10} automorphism008
    automorphism008_hole automorphism008_root (by decide +kernel) (rep001 halph)

def automorphism048 : Equiv.Perm Point where
  toFun := ![9,10,2,8,5,4,7,6,3,0,1,11,12]
  invFun := ![9,10,2,8,5,4,7,6,3,0,1,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism048_hole : automorphism048 hole = hole := by decide +kernel

theorem automorphism048_root : transport automorphism048 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism048 (by decide +kernel)

theorem query362 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,7,9,10} :=
  obstruction_transport figure6 FastDual68_001.points {2,7,9,10} automorphism048
    automorphism048_hole automorphism048_root (by decide +kernel) (rep001 halph)

def automorphism049 : Equiv.Perm Point where
  toFun := ![2,10,9,8,5,4,11,1,0,3,6,7,12]
  invFun := ![8,7,0,9,5,4,10,11,3,2,1,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism049_hole : automorphism049 hole = hole := by decide +kernel

theorem automorphism049_root : transport automorphism049 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism049 (by decide +kernel)

theorem query368 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,9,10,11} :=
  obstruction_transport figure6 FastDual68_001.points {2,9,10,11} automorphism049
    automorphism049_hole automorphism049_root (by decide +kernel) (rep001 halph)

def automorphism050 : Equiv.Perm Point where
  toFun := ![9,6,3,0,5,4,7,10,2,8,11,1,12]
  invFun := ![3,11,8,2,5,4,1,6,9,0,7,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism050_hole : automorphism050 hole = hole := by decide +kernel

theorem automorphism050_root : transport automorphism050 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism050 (by decide +kernel)

theorem query406 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,6,7,9} :=
  obstruction_transport figure6 FastDual68_001.points {3,6,7,9} automorphism050
    automorphism050_hole automorphism050_root (by decide +kernel) (rep001 halph)

def automorphism051 : Equiv.Perm Point where
  toFun := ![10,7,3,1,5,4,6,9,2,8,11,0,12]
  invFun := ![11,3,8,2,5,4,6,1,9,7,0,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism051_hole : automorphism051 hole = hole := by decide +kernel

theorem automorphism051_root : transport automorphism051 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism051 (by decide +kernel)

theorem query407 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,6,7,10} :=
  obstruction_transport figure6 FastDual68_001.points {3,6,7,10} automorphism051
    automorphism051_hole automorphism051_root (by decide +kernel) (rep001 halph)

theorem query409 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,6,8,9} :=
  obstruction_transport figure6 FastDual68_001.points {3,6,8,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep001 halph)

def automorphism052 : Equiv.Perm Point where
  toFun := ![11,8,3,2,5,4,6,9,1,7,10,0,12]
  invFun := ![11,8,3,2,5,4,6,9,1,7,10,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism052_hole : automorphism052 hole = hole := by decide +kernel

theorem automorphism052_root : transport automorphism052 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism052 (by decide +kernel)

theorem query411 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,6,8,11} :=
  obstruction_transport figure6 FastDual68_001.points {3,6,8,11} automorphism052
    automorphism052_hole automorphism052_root (by decide +kernel) (rep001 halph)

def automorphism053 : Equiv.Perm Point where
  toFun := ![6,9,3,0,5,4,10,7,2,11,8,1,12]
  invFun := ![3,11,8,2,5,4,0,7,10,1,6,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism053_hole : automorphism053 hole = hole := by decide +kernel

theorem automorphism053_root : transport automorphism053 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism053 (by decide +kernel)

theorem query412 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,6,9,10} :=
  obstruction_transport figure6 FastDual68_001.points {3,6,9,10} automorphism053
    automorphism053_hole automorphism053_root (by decide +kernel) (rep001 halph)

def automorphism054 : Equiv.Perm Point where
  toFun := ![6,9,3,0,5,4,11,8,1,10,7,2,12]
  invFun := ![3,8,11,2,5,4,0,10,7,1,9,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism054_hole : automorphism054 hole = hole := by decide +kernel

theorem automorphism054_root : transport automorphism054 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism054 (by decide +kernel)

theorem query413 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,6,9,11} :=
  obstruction_transport figure6 FastDual68_001.points {3,6,9,11} automorphism054
    automorphism054_hole automorphism054_root (by decide +kernel) (rep001 halph)

theorem query416 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,7,8,10} :=
  obstruction_transport figure6 FastDual68_001.points {3,7,8,10} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep001 halph)

theorem query417 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,7,8,11} :=
  obstruction_transport figure6 FastDual68_001.points {3,7,8,11} automorphism006
    automorphism006_hole automorphism006_root (by decide +kernel) (rep001 halph)

def automorphism055 : Equiv.Perm Point where
  toFun := ![7,10,3,1,5,4,9,6,2,11,8,0,12]
  invFun := ![11,3,8,2,5,4,7,0,10,6,1,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism055_hole : automorphism055 hole = hole := by decide +kernel

theorem automorphism055_root : transport automorphism055 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism055 (by decide +kernel)

theorem query418 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,7,9,10} :=
  obstruction_transport figure6 FastDual68_001.points {3,7,9,10} automorphism055
    automorphism055_hole automorphism055_root (by decide +kernel) (rep001 halph)

def automorphism056 : Equiv.Perm Point where
  toFun := ![7,10,3,1,5,4,11,8,0,9,6,2,12]
  invFun := ![8,3,11,2,5,4,10,0,7,9,1,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism056_hole : automorphism056 hole = hole := by decide +kernel

theorem automorphism056_root : transport automorphism056 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism056 (by decide +kernel)

theorem query420 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,7,10,11} :=
  obstruction_transport figure6 FastDual68_001.points {3,7,10,11} automorphism056
    automorphism056_hole automorphism056_root (by decide +kernel) (rep001 halph)

def automorphism057 : Equiv.Perm Point where
  toFun := ![8,11,3,2,5,4,9,6,1,10,7,0,12]
  invFun := ![11,8,3,2,5,4,7,10,0,6,9,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism057_hole : automorphism057 hole = hole := by decide +kernel

theorem automorphism057_root : transport automorphism057 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism057 (by decide +kernel)

theorem query422 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,8,9,11} :=
  obstruction_transport figure6 FastDual68_001.points {3,8,9,11} automorphism057
    automorphism057_hole automorphism057_root (by decide +kernel) (rep001 halph)

def automorphism058 : Equiv.Perm Point where
  toFun := ![8,11,3,2,5,4,10,7,0,9,6,1,12]
  invFun := ![8,11,3,2,5,4,10,7,0,9,6,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism058_hole : automorphism058 hole = hole := by decide +kernel

theorem automorphism058_root : transport automorphism058 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism058 (by decide +kernel)

theorem query423 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,8,10,11} :=
  obstruction_transport figure6 FastDual68_001.points {3,8,10,11} automorphism058
    automorphism058_hole automorphism058_root (by decide +kernel) (rep001 halph)

theorem rep002 (halph : AlphabetComplete figure6 alphabets) :
    ActualObstruction figure6 FastDual68_002.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction figure6 rootCodes root_binding alphabets halph nonincident_complete
    FastDual68_002.pointList FastDual68_002.columns FastDual68_002.rows FastDual68_002.bound (by decide +kernel)
    FastDual68_002.column_mask FastDual68_002.checked hc F hF hroot hmin hout

theorem query011 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,3,6} := rep002 halph

def automorphism059 : Equiv.Perm Point where
  toFun := ![3,7,10,1,5,4,0,11,8,2,9,6,12]
  invFun := ![6,3,9,0,5,4,11,1,8,10,2,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism059_hole : automorphism059 hole = hole := by decide +kernel

theorem automorphism059_root : transport automorphism059 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism059 (by decide +kernel)

theorem query012 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,3,7} :=
  obstruction_transport figure6 FastDual68_002.points {0,1,3,7} automorphism059
    automorphism059_hole automorphism059_root (by decide +kernel) (rep002 halph)

theorem query014 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,3,9} :=
  obstruction_transport figure6 FastDual68_002.points {0,1,3,9} automorphism035
    automorphism035_hole automorphism035_root (by decide +kernel) (rep002 halph)

theorem query015 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,3,10} :=
  obstruction_transport figure6 FastDual68_002.points {0,1,3,10} automorphism023
    automorphism023_hole automorphism023_root (by decide +kernel) (rep002 halph)

def automorphism060 : Equiv.Perm Point where
  toFun := ![10,0,11,6,5,4,1,9,2,8,3,7,12]
  invFun := ![1,6,8,10,5,4,3,11,9,7,0,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism060_hole : automorphism060 hole = hole := by decide +kernel

theorem automorphism060_root : transport automorphism060 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism060 (by decide +kernel)

theorem query033 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,6,10} :=
  obstruction_transport figure6 FastDual68_002.points {0,1,6,10} automorphism060
    automorphism060_hole automorphism060_root (by decide +kernel) (rep002 halph)

def automorphism061 : Equiv.Perm Point where
  toFun := ![9,1,11,7,5,4,0,10,2,8,3,6,12]
  invFun := ![6,1,8,10,5,4,11,3,9,0,7,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism061_hole : automorphism061 hole = hole := by decide +kernel

theorem automorphism061_root : transport automorphism061 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism061 (by decide +kernel)

theorem query036 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,7,9} :=
  obstruction_transport figure6 FastDual68_002.points {0,1,7,9} automorphism061
    automorphism061_hole automorphism061_root (by decide +kernel) (rep002 halph)

def automorphism062 : Equiv.Perm Point where
  toFun := ![3,6,9,0,5,4,2,10,7,1,11,8,12]
  invFun := ![3,9,6,0,5,4,1,8,11,2,7,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism062_hole : automorphism062 hole = hole := by decide +kernel

theorem automorphism062_root : transport automorphism062 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism062 (by decide +kernel)

theorem query047 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,3,6} :=
  obstruction_transport figure6 FastDual68_002.points {0,2,3,6} automorphism062
    automorphism062_hole automorphism062_root (by decide +kernel) (rep002 halph)

def automorphism063 : Equiv.Perm Point where
  toFun := ![3,8,11,2,5,4,0,10,7,1,9,6,12]
  invFun := ![6,9,3,0,5,4,11,8,1,10,7,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism063_hole : automorphism063 hole = hole := by decide +kernel

theorem automorphism063_root : transport automorphism063 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism063 (by decide +kernel)

theorem query049 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,3,8} :=
  obstruction_transport figure6 FastDual68_002.points {0,2,3,8} automorphism063
    automorphism063_hole automorphism063_root (by decide +kernel) (rep002 halph)

theorem query050 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,3,9} :=
  obstruction_transport figure6 FastDual68_002.points {0,2,3,9} automorphism043
    automorphism043_hole automorphism043_root (by decide +kernel) (rep002 halph)

theorem query052 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,3,11} :=
  obstruction_transport figure6 FastDual68_002.points {0,2,3,11} automorphism024
    automorphism024_hole automorphism024_root (by decide +kernel) (rep002 halph)

def automorphism064 : Equiv.Perm Point where
  toFun := ![11,0,10,6,5,4,2,9,1,7,3,8,12]
  invFun := ![1,8,6,10,5,4,3,9,11,7,2,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism064_hole : automorphism064 hole = hole := by decide +kernel

theorem automorphism064_root : transport automorphism064 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism064 (by decide +kernel)

theorem query070 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,6,11} :=
  obstruction_transport figure6 FastDual68_002.points {0,2,6,11} automorphism064
    automorphism064_hole automorphism064_root (by decide +kernel) (rep002 halph)

def automorphism065 : Equiv.Perm Point where
  toFun := ![9,2,10,8,5,4,0,11,1,7,3,6,12]
  invFun := ![6,8,1,10,5,4,11,9,3,0,2,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism065_hole : automorphism065 hole = hole := by decide +kernel

theorem automorphism065_root : transport automorphism065 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism065 (by decide +kernel)

theorem query075 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,8,9} :=
  obstruction_transport figure6 FastDual68_002.points {0,2,8,9} automorphism065
    automorphism065_hole automorphism065_root (by decide +kernel) (rep002 halph)

def automorphism066 : Equiv.Perm Point where
  toFun := ![6,3,9,0,5,4,10,2,7,11,1,8,12]
  invFun := ![3,10,7,1,5,4,0,8,11,2,6,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism066_hole : automorphism066 hole = hole := by decide +kernel

theorem automorphism066_root : transport automorphism066 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism066 (by decide +kernel)

theorem query097 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,3,6,10} :=
  obstruction_transport figure6 FastDual68_002.points {0,3,6,10} automorphism066
    automorphism066_hole automorphism066_root (by decide +kernel) (rep002 halph)

def automorphism067 : Equiv.Perm Point where
  toFun := ![6,3,9,0,5,4,11,1,8,10,2,7,12]
  invFun := ![3,7,10,1,5,4,0,11,8,2,9,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism067_hole : automorphism067 hole = hole := by decide +kernel

theorem automorphism067_root : transport automorphism067 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism067 (by decide +kernel)

theorem query098 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,3,6,11} :=
  obstruction_transport figure6 FastDual68_002.points {0,3,6,11} automorphism067
    automorphism067_hole automorphism067_root (by decide +kernel) (rep002 halph)

def automorphism068 : Equiv.Perm Point where
  toFun := ![9,3,6,0,5,4,7,2,10,8,1,11,12]
  invFun := ![3,10,7,1,5,4,2,6,9,0,8,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism068_hole : automorphism068 hole = hole := by decide +kernel

theorem automorphism068_root : transport automorphism068 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism068 (by decide +kernel)

theorem query100 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,3,7,9} :=
  obstruction_transport figure6 FastDual68_002.points {0,3,7,9} automorphism068
    automorphism068_hole automorphism068_root (by decide +kernel) (rep002 halph)

def automorphism069 : Equiv.Perm Point where
  toFun := ![9,3,6,0,5,4,8,1,11,7,2,10,12]
  invFun := ![3,7,10,1,5,4,2,9,6,0,11,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism069_hole : automorphism069 hole = hole := by decide +kernel

theorem automorphism069_root : transport automorphism069 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism069 (by decide +kernel)

theorem query103 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,3,8,9} :=
  obstruction_transport figure6 FastDual68_002.points {0,3,8,9} automorphism069
    automorphism069_hole automorphism069_root (by decide +kernel) (rep002 halph)

theorem query146 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,6,7,9} :=
  obstruction_transport figure6 FastDual68_002.points {0,6,7,9} automorphism050
    automorphism050_hole automorphism050_root (by decide +kernel) (rep002 halph)

def automorphism070 : Equiv.Perm Point where
  toFun := ![11,0,10,6,5,4,7,3,8,2,9,1,12]
  invFun := ![1,11,9,7,5,4,3,6,8,10,2,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism070_hole : automorphism070 hole = hole := by decide +kernel

theorem automorphism070_root : transport automorphism070 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism070 (by decide +kernel)

theorem query148 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,6,7,11} :=
  obstruction_transport figure6 FastDual68_002.points {0,6,7,11} automorphism070
    automorphism070_hole automorphism070_root (by decide +kernel) (rep002 halph)

theorem query149 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,6,8,9} :=
  obstruction_transport figure6 FastDual68_002.points {0,6,8,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep002 halph)

def automorphism071 : Equiv.Perm Point where
  toFun := ![10,0,11,6,5,4,8,3,7,1,9,2,12]
  invFun := ![1,9,11,7,5,4,3,8,6,10,0,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism071_hole : automorphism071 hole = hole := by decide +kernel

theorem automorphism071_root : transport automorphism071 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism071 (by decide +kernel)

theorem query150 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,6,8,10} :=
  obstruction_transport figure6 FastDual68_002.points {0,6,8,10} automorphism071
    automorphism071_hole automorphism071_root (by decide +kernel) (rep002 halph)

theorem query152 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,6,9,10} :=
  obstruction_transport figure6 FastDual68_002.points {0,6,9,10} automorphism053
    automorphism053_hole automorphism053_root (by decide +kernel) (rep002 halph)

theorem query153 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,6,9,11} :=
  obstruction_transport figure6 FastDual68_002.points {0,6,9,11} automorphism054
    automorphism054_hole automorphism054_root (by decide +kernel) (rep002 halph)

theorem query159 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,7,9,11} :=
  obstruction_transport figure6 FastDual68_002.points {0,7,9,11} automorphism016
    automorphism016_hole automorphism016_root (by decide +kernel) (rep002 halph)

theorem query161 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,8,9,10} :=
  obstruction_transport figure6 FastDual68_002.points {0,8,9,10} automorphism020
    automorphism020_hole automorphism020_root (by decide +kernel) (rep002 halph)

def automorphism072 : Equiv.Perm Point where
  toFun := ![3,7,10,1,5,4,2,9,6,0,11,8,12]
  invFun := ![9,3,6,0,5,4,8,1,11,7,2,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism072_hole : automorphism072 hole = hole := by decide +kernel

theorem automorphism072_root : transport automorphism072 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism072 (by decide +kernel)

theorem query168 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,3,7} :=
  obstruction_transport figure6 FastDual68_002.points {1,2,3,7} automorphism072
    automorphism072_hole automorphism072_root (by decide +kernel) (rep002 halph)

def automorphism073 : Equiv.Perm Point where
  toFun := ![3,8,11,2,5,4,1,9,6,0,10,7,12]
  invFun := ![9,6,3,0,5,4,8,11,1,7,10,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism073_hole : automorphism073 hole = hole := by decide +kernel

theorem automorphism073_root : transport automorphism073 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism073 (by decide +kernel)

theorem query169 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,3,8} :=
  obstruction_transport figure6 FastDual68_002.points {1,2,3,8} automorphism073
    automorphism073_hole automorphism073_root (by decide +kernel) (rep002 halph)

theorem query171 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,3,10} :=
  obstruction_transport figure6 FastDual68_002.points {1,2,3,10} automorphism044
    automorphism044_hole automorphism044_root (by decide +kernel) (rep002 halph)

theorem query172 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,3,11} :=
  obstruction_transport figure6 FastDual68_002.points {1,2,3,11} automorphism036
    automorphism036_hole automorphism036_root (by decide +kernel) (rep002 halph)

def automorphism074 : Equiv.Perm Point where
  toFun := ![11,1,9,7,5,4,2,10,0,6,3,8,12]
  invFun := ![8,1,6,10,5,4,9,3,11,2,7,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism074_hole : automorphism074 hole = hole := by decide +kernel

theorem automorphism074_root : transport automorphism074 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism074 (by decide +kernel)

theorem query194 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,7,11} :=
  obstruction_transport figure6 FastDual68_002.points {1,2,7,11} automorphism074
    automorphism074_hole automorphism074_root (by decide +kernel) (rep002 halph)

def automorphism075 : Equiv.Perm Point where
  toFun := ![10,2,9,8,5,4,1,11,0,6,3,7,12]
  invFun := ![8,6,1,10,5,4,9,11,3,2,0,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism075_hole : automorphism075 hole = hole := by decide +kernel

theorem automorphism075_root : transport automorphism075 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism075 (by decide +kernel)

theorem query196 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,8,10} :=
  obstruction_transport figure6 FastDual68_002.points {1,2,8,10} automorphism075
    automorphism075_hole automorphism075_root (by decide +kernel) (rep002 halph)

def automorphism076 : Equiv.Perm Point where
  toFun := ![10,3,7,1,5,4,6,2,9,8,0,11,12]
  invFun := ![10,3,7,1,5,4,6,2,9,8,0,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism076_hole : automorphism076 hole = hole := by decide +kernel

theorem automorphism076_root : transport automorphism076 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism076 (by decide +kernel)

theorem query217 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,3,6,10} :=
  obstruction_transport figure6 FastDual68_002.points {1,3,6,10} automorphism076
    automorphism076_hole automorphism076_root (by decide +kernel) (rep002 halph)

def automorphism077 : Equiv.Perm Point where
  toFun := ![7,3,10,1,5,4,9,2,6,11,0,8,12]
  invFun := ![10,3,7,1,5,4,8,0,11,6,2,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism077_hole : automorphism077 hole = hole := by decide +kernel

theorem automorphism077_root : transport automorphism077 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism077 (by decide +kernel)

theorem query220 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,3,7,9} :=
  obstruction_transport figure6 FastDual68_002.points {1,3,7,9} automorphism077
    automorphism077_hole automorphism077_root (by decide +kernel) (rep002 halph)

def automorphism078 : Equiv.Perm Point where
  toFun := ![7,3,10,1,5,4,11,0,8,9,2,6,12]
  invFun := ![7,3,10,1,5,4,11,0,8,9,2,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism078_hole : automorphism078 hole = hole := by decide +kernel

theorem automorphism078_root : transport automorphism078 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism078 (by decide +kernel)

theorem query222 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,3,7,11} :=
  obstruction_transport figure6 FastDual68_002.points {1,3,7,11} automorphism078
    automorphism078_hole automorphism078_root (by decide +kernel) (rep002 halph)

def automorphism079 : Equiv.Perm Point where
  toFun := ![10,3,7,1,5,4,8,0,11,6,2,9,12]
  invFun := ![7,3,10,1,5,4,9,2,6,11,0,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism079_hole : automorphism079 hole = hole := by decide +kernel

theorem automorphism079_root : transport automorphism079 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism079 (by decide +kernel)

theorem query224 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,3,8,10} :=
  obstruction_transport figure6 FastDual68_002.points {1,3,8,10} automorphism079
    automorphism079_hole automorphism079_root (by decide +kernel) (rep002 halph)

theorem query267 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,6,7,10} :=
  obstruction_transport figure6 FastDual68_002.points {1,6,7,10} automorphism051
    automorphism051_hole automorphism051_root (by decide +kernel) (rep002 halph)

def automorphism080 : Equiv.Perm Point where
  toFun := ![11,1,9,7,5,4,6,3,8,2,10,0,12]
  invFun := ![11,1,9,7,5,4,6,3,8,2,10,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism080_hole : automorphism080 hole = hole := by decide +kernel

theorem automorphism080_root : transport automorphism080 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism080 (by decide +kernel)

theorem query268 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,6,7,11} :=
  obstruction_transport figure6 FastDual68_002.points {1,6,7,11} automorphism080
    automorphism080_hole automorphism080_root (by decide +kernel) (rep002 halph)

theorem query274 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,6,10,11} :=
  obstruction_transport figure6 FastDual68_002.points {1,6,10,11} automorphism017
    automorphism017_hole automorphism017_root (by decide +kernel) (rep002 halph)

def automorphism081 : Equiv.Perm Point where
  toFun := ![9,1,11,7,5,4,8,3,6,0,10,2,12]
  invFun := ![9,1,11,7,5,4,8,3,6,0,10,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism081_hole : automorphism081 hole = hole := by decide +kernel

theorem automorphism081_root : transport automorphism081 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism081 (by decide +kernel)

theorem query275 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,7,8,9} :=
  obstruction_transport figure6 FastDual68_002.points {1,7,8,9} automorphism081
    automorphism081_hole automorphism081_root (by decide +kernel) (rep002 halph)

theorem query276 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,7,8,10} :=
  obstruction_transport figure6 FastDual68_002.points {1,7,8,10} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep002 halph)

theorem query278 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,7,9,10} :=
  obstruction_transport figure6 FastDual68_002.points {1,7,9,10} automorphism055
    automorphism055_hole automorphism055_root (by decide +kernel) (rep002 halph)

theorem query280 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,7,10,11} :=
  obstruction_transport figure6 FastDual68_002.points {1,7,10,11} automorphism056
    automorphism056_hole automorphism056_root (by decide +kernel) (rep002 halph)

theorem query281 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,8,9,10} :=
  obstruction_transport figure6 FastDual68_002.points {1,8,9,10} automorphism032
    automorphism032_hole automorphism032_root (by decide +kernel) (rep002 halph)

def automorphism082 : Equiv.Perm Point where
  toFun := ![11,3,8,2,5,4,6,1,9,7,0,10,12]
  invFun := ![10,7,3,1,5,4,6,9,2,8,11,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism082_hole : automorphism082 hole = hole := by decide +kernel

theorem automorphism082_root : transport automorphism082 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism082 (by decide +kernel)

theorem query302 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,3,6,11} :=
  obstruction_transport figure6 FastDual68_002.points {2,3,6,11} automorphism082
    automorphism082_hole automorphism082_root (by decide +kernel) (rep002 halph)

def automorphism083 : Equiv.Perm Point where
  toFun := ![11,3,8,2,5,4,7,0,10,6,1,9,12]
  invFun := ![7,10,3,1,5,4,9,6,2,11,8,0,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism083_hole : automorphism083 hole = hole := by decide +kernel

theorem automorphism083_root : transport automorphism083 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism083 (by decide +kernel)

theorem query306 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,3,7,11} :=
  obstruction_transport figure6 FastDual68_002.points {2,3,7,11} automorphism083
    automorphism083_hole automorphism083_root (by decide +kernel) (rep002 halph)

def automorphism084 : Equiv.Perm Point where
  toFun := ![8,3,11,2,5,4,9,1,6,10,0,7,12]
  invFun := ![10,7,3,1,5,4,8,11,0,6,9,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism084_hole : automorphism084 hole = hole := by decide +kernel

theorem automorphism084_root : transport automorphism084 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism084 (by decide +kernel)

theorem query307 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,3,8,9} :=
  obstruction_transport figure6 FastDual68_002.points {2,3,8,9} automorphism084
    automorphism084_hole automorphism084_root (by decide +kernel) (rep002 halph)

def automorphism085 : Equiv.Perm Point where
  toFun := ![8,3,11,2,5,4,10,0,7,9,1,6,12]
  invFun := ![7,10,3,1,5,4,11,8,0,9,6,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism085_hole : automorphism085 hole = hole := by decide +kernel

theorem automorphism085_root : transport automorphism085 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism085 (by decide +kernel)

theorem query308 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,3,8,10} :=
  obstruction_transport figure6 FastDual68_002.points {2,3,8,10} automorphism085
    automorphism085_hole automorphism085_root (by decide +kernel) (rep002 halph)

def automorphism086 : Equiv.Perm Point where
  toFun := ![10,2,9,8,5,4,6,3,7,1,11,0,12]
  invFun := ![11,9,1,7,5,4,6,8,3,2,0,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism086_hole : automorphism086 hole = hole := by decide +kernel

theorem automorphism086_root : transport automorphism086 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism086 (by decide +kernel)

theorem query354 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,6,8,10} :=
  obstruction_transport figure6 FastDual68_002.points {2,6,8,10} automorphism086
    automorphism086_hole automorphism086_root (by decide +kernel) (rep002 halph)

theorem query355 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,6,8,11} :=
  obstruction_transport figure6 FastDual68_002.points {2,6,8,11} automorphism052
    automorphism052_hole automorphism052_root (by decide +kernel) (rep002 halph)

theorem query358 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,6,10,11} :=
  obstruction_transport figure6 FastDual68_002.points {2,6,10,11} automorphism021
    automorphism021_hole automorphism021_root (by decide +kernel) (rep002 halph)

def automorphism087 : Equiv.Perm Point where
  toFun := ![9,2,10,8,5,4,7,3,6,0,11,1,12]
  invFun := ![9,11,1,7,5,4,8,6,3,0,2,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism087_hole : automorphism087 hole = hole := by decide +kernel

theorem automorphism087_root : transport automorphism087 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism087 (by decide +kernel)

theorem query359 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,7,8,9} :=
  obstruction_transport figure6 FastDual68_002.points {2,7,8,9} automorphism087
    automorphism087_hole automorphism087_root (by decide +kernel) (rep002 halph)

theorem query361 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,7,8,11} :=
  obstruction_transport figure6 FastDual68_002.points {2,7,8,11} automorphism006
    automorphism006_hole automorphism006_root (by decide +kernel) (rep002 halph)

theorem query363 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,7,9,11} :=
  obstruction_transport figure6 FastDual68_002.points {2,7,9,11} automorphism033
    automorphism033_hole automorphism033_root (by decide +kernel) (rep002 halph)

theorem query366 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,8,9,11} :=
  obstruction_transport figure6 FastDual68_002.points {2,8,9,11} automorphism057
    automorphism057_hole automorphism057_root (by decide +kernel) (rep002 halph)

theorem query367 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,8,10,11} :=
  obstruction_transport figure6 FastDual68_002.points {2,8,10,11} automorphism058
    automorphism058_hole automorphism058_root (by decide +kernel) (rep002 halph)

theorem query484 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {6,7,9,11} :=
  obstruction_transport figure6 FastDual68_002.points {6,7,9,11} automorphism005
    automorphism005_hole automorphism005_root (by decide +kernel) (rep002 halph)

theorem query485 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {6,7,10,11} :=
  obstruction_transport figure6 FastDual68_002.points {6,7,10,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep002 halph)

theorem query486 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {6,8,9,10} :=
  obstruction_transport figure6 FastDual68_002.points {6,8,9,10} automorphism008
    automorphism008_hole automorphism008_root (by decide +kernel) (rep002 halph)

theorem query488 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {6,8,10,11} :=
  obstruction_transport figure6 FastDual68_002.points {6,8,10,11} automorphism028
    automorphism028_hole automorphism028_root (by decide +kernel) (rep002 halph)

theorem query490 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {7,8,9,10} :=
  obstruction_transport figure6 FastDual68_002.points {7,8,9,10} automorphism048
    automorphism048_hole automorphism048_root (by decide +kernel) (rep002 halph)

theorem query491 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {7,8,9,11} :=
  obstruction_transport figure6 FastDual68_002.points {7,8,9,11} automorphism040
    automorphism040_hole automorphism040_root (by decide +kernel) (rep002 halph)

theorem rep003 (halph : AlphabetComplete figure6 alphabets) :
    ActualObstruction figure6 FastDual68_003.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction figure6 rootCodes root_binding alphabets halph nonincident_complete
    FastDual68_003.pointList FastDual68_003.columns FastDual68_003.rows FastDual68_003.bound (by decide +kernel)
    FastDual68_003.column_mask FastDual68_003.checked hc F hF hroot hmin hout

theorem query013 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,3,8} := rep003 halph

def automorphism088 : Equiv.Perm Point where
  toFun := ![1,0,2,3,5,4,10,9,11,7,6,8,12]
  invFun := ![1,0,2,3,5,4,10,9,11,7,6,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism088_hole : automorphism088 hole = hole := by decide +kernel

theorem automorphism088_root : transport automorphism088 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism088 (by decide +kernel)

theorem query016 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,3,11} :=
  obstruction_transport figure6 FastDual68_003.points {0,1,3,11} automorphism088
    automorphism088_hole automorphism088_root (by decide +kernel) (rep003 halph)

theorem query032 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,6,9} :=
  obstruction_transport figure6 FastDual68_003.points {0,1,6,9} automorphism000
    automorphism000_hole automorphism000_root (by decide +kernel) (rep003 halph)

theorem query034 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,6,11} :=
  obstruction_transport figure6 FastDual68_003.points {0,1,6,11} automorphism064
    automorphism064_hole automorphism064_root (by decide +kernel) (rep003 halph)

theorem query037 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,7,10} :=
  obstruction_transport figure6 FastDual68_003.points {0,1,7,10} automorphism003
    automorphism003_hole automorphism003_root (by decide +kernel) (rep003 halph)

theorem query038 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,7,11} :=
  obstruction_transport figure6 FastDual68_003.points {0,1,7,11} automorphism074
    automorphism074_hole automorphism074_root (by decide +kernel) (rep003 halph)

def automorphism089 : Equiv.Perm Point where
  toFun := ![8,0,7,9,5,4,2,6,1,10,3,11,12]
  invFun := ![1,8,6,10,5,4,7,2,0,3,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism089_hole : automorphism089 hole = hole := by decide +kernel

theorem automorphism089_root : transport automorphism089 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism089 (by decide +kernel)

theorem query039 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,8,9} :=
  obstruction_transport figure6 FastDual68_003.points {0,1,8,9} automorphism089
    automorphism089_hole automorphism089_root (by decide +kernel) (rep003 halph)

def automorphism090 : Equiv.Perm Point where
  toFun := ![8,1,6,10,5,4,2,7,0,9,3,11,12]
  invFun := ![8,1,6,10,5,4,2,7,0,9,3,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism090_hole : automorphism090 hole = hole := by decide +kernel

theorem automorphism090_root : transport automorphism090 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism090 (by decide +kernel)

theorem query040 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,8,10} :=
  obstruction_transport figure6 FastDual68_003.points {0,1,8,10} automorphism090
    automorphism090_hole automorphism090_root (by decide +kernel) (rep003 halph)

def automorphism091 : Equiv.Perm Point where
  toFun := ![2,0,1,3,5,4,8,6,7,11,9,10,12]
  invFun := ![1,2,0,3,5,4,7,8,6,10,11,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism091_hole : automorphism091 hole = hole := by decide +kernel

theorem automorphism091_root : transport automorphism091 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism091 (by decide +kernel)

theorem query048 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,3,7} :=
  obstruction_transport figure6 FastDual68_003.points {0,2,3,7} automorphism091
    automorphism091_hole automorphism091_root (by decide +kernel) (rep003 halph)

def automorphism092 : Equiv.Perm Point where
  toFun := ![2,0,1,3,5,4,11,9,10,8,6,7,12]
  invFun := ![1,2,0,3,5,4,10,11,9,7,8,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism092_hole : automorphism092 hole = hole := by decide +kernel

theorem automorphism092_root : transport automorphism092 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism092 (by decide +kernel)

theorem query051 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,3,10} :=
  obstruction_transport figure6 FastDual68_003.points {0,2,3,10} automorphism092
    automorphism092_hole automorphism092_root (by decide +kernel) (rep003 halph)

theorem query068 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,6,9} :=
  obstruction_transport figure6 FastDual68_003.points {0,2,6,9} automorphism050
    automorphism050_hole automorphism050_root (by decide +kernel) (rep003 halph)

theorem query069 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,6,10} :=
  obstruction_transport figure6 FastDual68_003.points {0,2,6,10} automorphism060
    automorphism060_hole automorphism060_root (by decide +kernel) (rep003 halph)

def automorphism093 : Equiv.Perm Point where
  toFun := ![7,0,8,9,5,4,1,6,2,11,3,10,12]
  invFun := ![1,6,8,10,5,4,7,0,2,3,11,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism093_hole : automorphism093 hole = hole := by decide +kernel

theorem automorphism093_root : transport automorphism093 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism093 (by decide +kernel)

theorem query072 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,7,9} :=
  obstruction_transport figure6 FastDual68_003.points {0,2,7,9} automorphism093
    automorphism093_hole automorphism093_root (by decide +kernel) (rep003 halph)

def automorphism094 : Equiv.Perm Point where
  toFun := ![7,2,6,11,5,4,1,8,0,9,3,10,12]
  invFun := ![8,6,1,10,5,4,2,0,7,9,11,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism094_hole : automorphism094 hole = hole := by decide +kernel

theorem automorphism094_root : transport automorphism094 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism094 (by decide +kernel)

theorem query074 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,7,11} :=
  obstruction_transport figure6 FastDual68_003.points {0,2,7,11} automorphism094
    automorphism094_hole automorphism094_root (by decide +kernel) (rep003 halph)

theorem query076 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,8,10} :=
  obstruction_transport figure6 FastDual68_003.points {0,2,8,10} automorphism075
    automorphism075_hole automorphism075_root (by decide +kernel) (rep003 halph)

theorem query077 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,8,11} :=
  obstruction_transport figure6 FastDual68_003.points {0,2,8,11} automorphism006
    automorphism006_hole automorphism006_root (by decide +kernel) (rep003 halph)

theorem query094 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,3,6,7} :=
  obstruction_transport figure6 FastDual68_003.points {0,3,6,7} automorphism066
    automorphism066_hole automorphism066_root (by decide +kernel) (rep003 halph)

theorem query095 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,3,6,8} :=
  obstruction_transport figure6 FastDual68_003.points {0,3,6,8} automorphism067
    automorphism067_hole automorphism067_root (by decide +kernel) (rep003 halph)

theorem query106 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,3,9,10} :=
  obstruction_transport figure6 FastDual68_003.points {0,3,9,10} automorphism068
    automorphism068_hole automorphism068_root (by decide +kernel) (rep003 halph)

theorem query107 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,3,9,11} :=
  obstruction_transport figure6 FastDual68_003.points {0,3,9,11} automorphism069
    automorphism069_hole automorphism069_root (by decide +kernel) (rep003 halph)

theorem query147 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,6,7,10} :=
  obstruction_transport figure6 FastDual68_003.points {0,6,7,10} automorphism071
    automorphism071_hole automorphism071_root (by decide +kernel) (rep003 halph)

theorem query151 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,6,8,11} :=
  obstruction_transport figure6 FastDual68_003.points {0,6,8,11} automorphism070
    automorphism070_hole automorphism070_root (by decide +kernel) (rep003 halph)

def automorphism095 : Equiv.Perm Point where
  toFun := ![7,0,8,9,5,4,11,3,10,1,6,2,12]
  invFun := ![1,9,11,7,5,4,10,0,2,3,8,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism095_hole : automorphism095 hole = hole := by decide +kernel

theorem automorphism095_root : transport automorphism095 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism095 (by decide +kernel)

theorem query158 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,7,9,10} :=
  obstruction_transport figure6 FastDual68_003.points {0,7,9,10} automorphism095
    automorphism095_hole automorphism095_root (by decide +kernel) (rep003 halph)

def automorphism096 : Equiv.Perm Point where
  toFun := ![8,0,7,9,5,4,10,3,11,2,6,1,12]
  invFun := ![1,11,9,7,5,4,10,2,0,3,6,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism096_hole : automorphism096 hole = hole := by decide +kernel

theorem automorphism096_root : transport automorphism096 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism096 (by decide +kernel)

theorem query162 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,8,9,11} :=
  obstruction_transport figure6 FastDual68_003.points {0,8,9,11} automorphism096
    automorphism096_hole automorphism096_root (by decide +kernel) (rep003 halph)

theorem query167 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,3,6} :=
  obstruction_transport figure6 FastDual68_003.points {1,2,3,6} automorphism010
    automorphism010_hole automorphism010_root (by decide +kernel) (rep003 halph)

theorem query170 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,3,9} :=
  obstruction_transport figure6 FastDual68_003.points {1,2,3,9} automorphism013
    automorphism013_hole automorphism013_root (by decide +kernel) (rep003 halph)

def automorphism097 : Equiv.Perm Point where
  toFun := ![6,1,8,10,5,4,0,7,2,11,3,9,12]
  invFun := ![6,1,8,10,5,4,0,7,2,11,3,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism097_hole : automorphism097 hole = hole := by decide +kernel

theorem automorphism097_root : transport automorphism097 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism097 (by decide +kernel)

theorem query189 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,6,10} :=
  obstruction_transport figure6 FastDual68_003.points {1,2,6,10} automorphism097
    automorphism097_hole automorphism097_root (by decide +kernel) (rep003 halph)

def automorphism098 : Equiv.Perm Point where
  toFun := ![6,2,7,11,5,4,0,8,1,10,3,9,12]
  invFun := ![6,8,1,10,5,4,0,2,7,11,9,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism098_hole : automorphism098 hole = hole := by decide +kernel

theorem automorphism098_root : transport automorphism098 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism098 (by decide +kernel)

theorem query190 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,6,11} :=
  obstruction_transport figure6 FastDual68_003.points {1,2,6,11} automorphism098
    automorphism098_hole automorphism098_root (by decide +kernel) (rep003 halph)

theorem query192 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,7,9} :=
  obstruction_transport figure6 FastDual68_003.points {1,2,7,9} automorphism061
    automorphism061_hole automorphism061_root (by decide +kernel) (rep003 halph)

theorem query193 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,7,10} :=
  obstruction_transport figure6 FastDual68_003.points {1,2,7,10} automorphism051
    automorphism051_hole automorphism051_root (by decide +kernel) (rep003 halph)

theorem query195 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,8,9} :=
  obstruction_transport figure6 FastDual68_003.points {1,2,8,9} automorphism065
    automorphism065_hole automorphism065_root (by decide +kernel) (rep003 halph)

theorem query197 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,8,11} :=
  obstruction_transport figure6 FastDual68_003.points {1,2,8,11} automorphism052
    automorphism052_hole automorphism052_root (by decide +kernel) (rep003 halph)

theorem query214 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,3,6,7} :=
  obstruction_transport figure6 FastDual68_003.points {1,3,6,7} automorphism077
    automorphism077_hole automorphism077_root (by decide +kernel) (rep003 halph)

theorem query219 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,3,7,8} :=
  obstruction_transport figure6 FastDual68_003.points {1,3,7,8} automorphism078
    automorphism078_hole automorphism078_root (by decide +kernel) (rep003 halph)

theorem query226 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,3,9,10} :=
  obstruction_transport figure6 FastDual68_003.points {1,3,9,10} automorphism076
    automorphism076_hole automorphism076_root (by decide +kernel) (rep003 halph)

theorem query228 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,3,10,11} :=
  obstruction_transport figure6 FastDual68_003.points {1,3,10,11} automorphism079
    automorphism079_hole automorphism079_root (by decide +kernel) (rep003 halph)

theorem query266 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,6,7,9} :=
  obstruction_transport figure6 FastDual68_003.points {1,6,7,9} automorphism081
    automorphism081_hole automorphism081_root (by decide +kernel) (rep003 halph)

def automorphism099 : Equiv.Perm Point where
  toFun := ![6,1,8,10,5,4,11,3,9,0,7,2,12]
  invFun := ![9,1,11,7,5,4,0,10,2,8,3,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism099_hole : automorphism099 hole = hole := by decide +kernel

theorem automorphism099_root : transport automorphism099 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism099 (by decide +kernel)

theorem query272 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,6,9,10} :=
  obstruction_transport figure6 FastDual68_003.points {1,6,9,10} automorphism099
    automorphism099_hole automorphism099_root (by decide +kernel) (rep003 halph)

theorem query277 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,7,8,11} :=
  obstruction_transport figure6 FastDual68_003.points {1,7,8,11} automorphism080
    automorphism080_hole automorphism080_root (by decide +kernel) (rep003 halph)

def automorphism100 : Equiv.Perm Point where
  toFun := ![8,1,6,10,5,4,9,3,11,2,7,0,12]
  invFun := ![11,1,9,7,5,4,2,10,0,6,3,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism100_hole : automorphism100 hole = hole := by decide +kernel

theorem automorphism100_root : transport automorphism100 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism100 (by decide +kernel)

theorem query283 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,8,10,11} :=
  obstruction_transport figure6 FastDual68_003.points {1,8,10,11} automorphism100
    automorphism100_hole automorphism100_root (by decide +kernel) (rep003 halph)

theorem query299 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,3,6,8} :=
  obstruction_transport figure6 FastDual68_003.points {2,3,6,8} automorphism084
    automorphism084_hole automorphism084_root (by decide +kernel) (rep003 halph)

theorem query303 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,3,7,8} :=
  obstruction_transport figure6 FastDual68_003.points {2,3,7,8} automorphism085
    automorphism085_hole automorphism085_root (by decide +kernel) (rep003 halph)

theorem query311 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,3,9,11} :=
  obstruction_transport figure6 FastDual68_003.points {2,3,9,11} automorphism082
    automorphism082_hole automorphism082_root (by decide +kernel) (rep003 halph)

theorem query312 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,3,10,11} :=
  obstruction_transport figure6 FastDual68_003.points {2,3,10,11} automorphism083
    automorphism083_hole automorphism083_root (by decide +kernel) (rep003 halph)

theorem query353 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,6,8,9} :=
  obstruction_transport figure6 FastDual68_003.points {2,6,8,9} automorphism087
    automorphism087_hole automorphism087_root (by decide +kernel) (rep003 halph)

def automorphism101 : Equiv.Perm Point where
  toFun := ![6,2,7,11,5,4,10,3,9,0,8,1,12]
  invFun := ![9,11,1,7,5,4,0,2,10,8,6,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism101_hole : automorphism101 hole = hole := by decide +kernel

theorem automorphism101_root : transport automorphism101 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism101 (by decide +kernel)

theorem query357 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,6,9,11} :=
  obstruction_transport figure6 FastDual68_003.points {2,6,9,11} automorphism101
    automorphism101_hole automorphism101_root (by decide +kernel) (rep003 halph)

theorem query360 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,7,8,10} :=
  obstruction_transport figure6 FastDual68_003.points {2,7,8,10} automorphism086
    automorphism086_hole automorphism086_root (by decide +kernel) (rep003 halph)

def automorphism102 : Equiv.Perm Point where
  toFun := ![7,2,6,11,5,4,9,3,10,1,8,0,12]
  invFun := ![11,9,1,7,5,4,2,0,10,6,8,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem automorphism102_hole : automorphism102 hole = hole := by decide +kernel

theorem automorphism102_root : transport automorphism102 figure6 = figure6 :=
  root_symmetry_of_codes rootCodes figure6 root_binding automorphism102 (by decide +kernel)

theorem query364 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,7,10,11} :=
  obstruction_transport figure6 FastDual68_003.points {2,7,10,11} automorphism102
    automorphism102_hole automorphism102_root (by decide +kernel) (rep003 halph)

theorem query408 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,6,7,11} :=
  obstruction_transport figure6 FastDual68_003.points {3,6,7,11} automorphism007
    automorphism007_hole automorphism007_root (by decide +kernel) (rep003 halph)

theorem query410 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,6,8,10} :=
  obstruction_transport figure6 FastDual68_003.points {3,6,8,10} automorphism004
    automorphism004_hole automorphism004_root (by decide +kernel) (rep003 halph)

theorem query414 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,6,10,11} :=
  obstruction_transport figure6 FastDual68_003.points {3,6,10,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep003 halph)

theorem query415 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,7,8,9} :=
  obstruction_transport figure6 FastDual68_003.points {3,7,8,9} automorphism002
    automorphism002_hole automorphism002_root (by decide +kernel) (rep003 halph)

theorem query419 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,7,9,11} :=
  obstruction_transport figure6 FastDual68_003.points {3,7,9,11} automorphism005
    automorphism005_hole automorphism005_root (by decide +kernel) (rep003 halph)

theorem query421 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {3,8,9,10} :=
  obstruction_transport figure6 FastDual68_003.points {3,8,9,10} automorphism008
    automorphism008_hole automorphism008_root (by decide +kernel) (rep003 halph)

theorem query480 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {6,7,8,9} :=
  obstruction_transport figure6 FastDual68_003.points {6,7,8,9} automorphism019
    automorphism019_hole automorphism019_root (by decide +kernel) (rep003 halph)

theorem query481 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {6,7,8,10} :=
  obstruction_transport figure6 FastDual68_003.points {6,7,8,10} automorphism031
    automorphism031_hole automorphism031_root (by decide +kernel) (rep003 halph)

theorem query482 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {6,7,8,11} :=
  obstruction_transport figure6 FastDual68_003.points {6,7,8,11} automorphism030
    automorphism030_hole automorphism030_root (by decide +kernel) (rep003 halph)

theorem query489 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {6,9,10,11} :=
  obstruction_transport figure6 FastDual68_003.points {6,9,10,11} automorphism021
    automorphism021_hole automorphism021_root (by decide +kernel) (rep003 halph)

theorem query493 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {7,9,10,11} :=
  obstruction_transport figure6 FastDual68_003.points {7,9,10,11} automorphism033
    automorphism033_hole automorphism033_root (by decide +kernel) (rep003 halph)

theorem query494 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {8,9,10,11} :=
  obstruction_transport figure6 FastDual68_003.points {8,9,10,11} automorphism032
    automorphism032_hole automorphism032_root (by decide +kernel) (rep003 halph)

theorem rep004 (halph : AlphabetComplete figure6 alphabets) :
    ActualObstruction figure6 FastDual68_004.points := by
  intro hc F hF hroot hmin hout
  exact fast_dual_actual_obstruction figure6 rootCodes root_binding alphabets halph nonincident_complete
    FastDual68_004.pointList FastDual68_004.columns FastDual68_004.rows FastDual68_004.bound (by decide +kernel)
    FastDual68_004.column_mask FastDual68_004.checked hc F hF hroot hmin hout

theorem query030 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,6,7} := rep004 halph

theorem query042 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,1,9,10} :=
  obstruction_transport figure6 FastDual68_004.points {0,1,9,10} automorphism032
    automorphism032_hole automorphism032_root (by decide +kernel) (rep004 halph)

theorem query067 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,6,8} :=
  obstruction_transport figure6 FastDual68_004.points {0,2,6,8} automorphism031
    automorphism031_hole automorphism031_root (by decide +kernel) (rep004 halph)

theorem query079 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,2,9,11} :=
  obstruction_transport figure6 FastDual68_004.points {0,2,9,11} automorphism033
    automorphism033_hole automorphism033_root (by decide +kernel) (rep004 halph)

theorem query102 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,3,7,11} :=
  obstruction_transport figure6 FastDual68_004.points {0,3,7,11} automorphism083
    automorphism083_hole automorphism083_root (by decide +kernel) (rep004 halph)

theorem query104 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {0,3,8,10} :=
  obstruction_transport figure6 FastDual68_004.points {0,3,8,10} automorphism079
    automorphism079_hole automorphism079_root (by decide +kernel) (rep004 halph)

theorem query191 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,7,8} :=
  obstruction_transport figure6 FastDual68_004.points {1,2,7,8} automorphism019
    automorphism019_hole automorphism019_root (by decide +kernel) (rep004 halph)

theorem query200 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,2,10,11} :=
  obstruction_transport figure6 FastDual68_004.points {1,2,10,11} automorphism021
    automorphism021_hole automorphism021_root (by decide +kernel) (rep004 halph)

theorem query218 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,3,6,11} :=
  obstruction_transport figure6 FastDual68_004.points {1,3,6,11} automorphism082
    automorphism082_hole automorphism082_root (by decide +kernel) (rep004 halph)

theorem query223 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {1,3,8,9} :=
  obstruction_transport figure6 FastDual68_004.points {1,3,8,9} automorphism069
    automorphism069_hole automorphism069_root (by decide +kernel) (rep004 halph)

theorem query301 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,3,6,10} :=
  obstruction_transport figure6 FastDual68_004.points {2,3,6,10} automorphism076
    automorphism076_hole automorphism076_root (by decide +kernel) (rep004 halph)

theorem query304 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {2,3,7,9} :=
  obstruction_transport figure6 FastDual68_004.points {2,3,7,9} automorphism068
    automorphism068_hole automorphism068_root (by decide +kernel) (rep004 halph)

theorem query483 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {6,7,9,10} :=
  obstruction_transport figure6 FastDual68_004.points {6,7,9,10} automorphism008
    automorphism008_hole automorphism008_root (by decide +kernel) (rep004 halph)

theorem query487 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {6,8,9,11} :=
  obstruction_transport figure6 FastDual68_004.points {6,8,9,11} automorphism005
    automorphism005_hole automorphism005_root (by decide +kernel) (rep004 halph)

theorem query492 (halph : AlphabetComplete figure6 alphabets) : ActualObstruction figure6 {7,8,10,11} :=
  obstruction_transport figure6 FastDual68_004.points {7,8,10,11} automorphism001
    automorphism001_hole automorphism001_root (by decide +kernel) (rep004 halph)

def hardQuads : List (Finset Point) := [{0,1,8,11},{0,2,7,10},{1,2,6,9},{3,6,7,8},{3,9,10,11}]

def dualQuads : List (Finset Point) := [{0,1,2,3},{0,3,6,9},{0,6,10,11},{0,7,8,9},{1,3,7,10},{1,6,8,10},{1,7,9,11},{2,3,8,11},{2,6,7,11},{2,8,9,10},{0,1,2,6},{0,1,2,7},{0,1,2,8},{0,1,2,9},{0,1,2,10},{0,1,2,11},{0,1,6,8},{0,1,7,8},{0,1,9,11},{0,1,10,11},{0,2,6,7},{0,2,7,8},{0,2,9,10},{0,2,10,11},{0,3,7,8},{0,3,7,10},{0,3,8,11},{0,3,10,11},{0,6,7,8},{0,7,8,10},{0,7,8,11},{0,7,10,11},{0,8,10,11},{0,9,10,11},{1,2,6,7},{1,2,6,8},{1,2,9,10},{1,2,9,11},{1,3,6,8},{1,3,6,9},{1,3,8,11},{1,3,9,11},{1,6,7,8},{1,6,8,9},{1,6,8,11},{1,6,9,11},{1,8,9,11},{1,9,10,11},{2,3,6,7},{2,3,6,9},{2,3,7,10},{2,3,9,10},{2,6,7,8},{2,6,7,9},{2,6,7,10},{2,6,9,10},{2,7,9,10},{2,9,10,11},{3,6,7,9},{3,6,7,10},{3,6,8,9},{3,6,8,11},{3,6,9,10},{3,6,9,11},{3,7,8,10},{3,7,8,11},{3,7,9,10},{3,7,10,11},{3,8,9,11},{3,8,10,11},{0,1,3,6},{0,1,3,7},{0,1,3,9},{0,1,3,10},{0,1,6,10},{0,1,7,9},{0,2,3,6},{0,2,3,8},{0,2,3,9},{0,2,3,11},{0,2,6,11},{0,2,8,9},{0,3,6,10},{0,3,6,11},{0,3,7,9},{0,3,8,9},{0,6,7,9},{0,6,7,11},{0,6,8,9},{0,6,8,10},{0,6,9,10},{0,6,9,11},{0,7,9,11},{0,8,9,10},{1,2,3,7},{1,2,3,8},{1,2,3,10},{1,2,3,11},{1,2,7,11},{1,2,8,10},{1,3,6,10},{1,3,7,9},{1,3,7,11},{1,3,8,10},{1,6,7,10},{1,6,7,11},{1,6,10,11},{1,7,8,9},{1,7,8,10},{1,7,9,10},{1,7,10,11},{1,8,9,10},{2,3,6,11},{2,3,7,11},{2,3,8,9},{2,3,8,10},{2,6,8,10},{2,6,8,11},{2,6,10,11},{2,7,8,9},{2,7,8,11},{2,7,9,11},{2,8,9,11},{2,8,10,11},{6,7,9,11},{6,7,10,11},{6,8,9,10},{6,8,10,11},{7,8,9,10},{7,8,9,11},{0,1,3,8},{0,1,3,11},{0,1,6,9},{0,1,6,11},{0,1,7,10},{0,1,7,11},{0,1,8,9},{0,1,8,10},{0,2,3,7},{0,2,3,10},{0,2,6,9},{0,2,6,10},{0,2,7,9},{0,2,7,11},{0,2,8,10},{0,2,8,11},{0,3,6,7},{0,3,6,8},{0,3,9,10},{0,3,9,11},{0,6,7,10},{0,6,8,11},{0,7,9,10},{0,8,9,11},{1,2,3,6},{1,2,3,9},{1,2,6,10},{1,2,6,11},{1,2,7,9},{1,2,7,10},{1,2,8,9},{1,2,8,11},{1,3,6,7},{1,3,7,8},{1,3,9,10},{1,3,10,11},{1,6,7,9},{1,6,9,10},{1,7,8,11},{1,8,10,11},{2,3,6,8},{2,3,7,8},{2,3,9,11},{2,3,10,11},{2,6,8,9},{2,6,9,11},{2,7,8,10},{2,7,10,11},{3,6,7,11},{3,6,8,10},{3,6,10,11},{3,7,8,9},{3,7,9,11},{3,8,9,10},{6,7,8,9},{6,7,8,10},{6,7,8,11},{6,9,10,11},{7,9,10,11},{8,9,10,11},{0,1,6,7},{0,1,9,10},{0,2,6,8},{0,2,9,11},{0,3,7,11},{0,3,8,10},{1,2,7,8},{1,2,10,11},{1,3,6,11},{1,3,8,9},{2,3,6,10},{2,3,7,9},{6,7,9,10},{6,8,9,11},{7,8,10,11},{0,1,8,11},{0,2,7,10},{1,2,6,9},{3,6,7,8},{3,9,10,11}]


end C13.Global.Relative.Source68
