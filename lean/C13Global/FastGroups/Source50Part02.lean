import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source50
namespace C13.Global.FastDual50_016
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,8]
def points : Finset C13.Point := {2,6,7,8}
def columns : List Code := [379,439,631,699,829,830,859,875,971,979,995,1371,1387,1402,1447,1453,1461,1595,1639,1646,1654,1691,1707,1721,1837,1852,1867,1882,1957,1987,2395,2411,2425,2455,2462,2486,2619,2647,2653,2677,2715,2731,2746,2846,2876,2891,2921,2966,3011,3131,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3611,3627,3635,3641,3642,3655,3661,3662,3669,3670,3676,3685,3686,3692,3700,3723,3737,3738,3753,3754,3768,3788]
def rows : List LinearRow := [⟨.covers 141,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 166,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 2752,1,1⟩,⟨.incident 7,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source50.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source50.rootCodes link50 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual50_016
namespace C13.Global.FastDual50_017
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,9]
def points : Finset C13.Point := {2,6,7,9}
def columns : List Code := [379,439,631,699,829,830,923,939,971,979,995,1339,1371,1387,1402,1447,1453,1461,1639,1646,1654,1691,1707,1721,1838,1852,1894,1931,1945,1987,2363,2395,2411,2425,2455,2462,2486,2647,2653,2677,2715,2731,2746,2845,2876,2901,2955,2986,3011,3131,3277,3278,3292,3308,3355,3371,3379,3385,3386,3403,3417,3418,3433,3434,3448,3463,3469,3470,3477,3478,3484,3493,3494,3500,3508,3532,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 77,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 197,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 210,1,2⟩,⟨.covers 226,1,1⟩,⟨.covers 212,1,2⟩,⟨.covers 228,1,2⟩,⟨.covers 1616,1,1⟩,⟨.covers 864,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 2880,1,1⟩,⟨.incident 6,8,-1⟩,⟨.incident 7,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source50.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source50.rootCodes link50 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual50_017
