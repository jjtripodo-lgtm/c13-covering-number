import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source57
namespace C13.Global.FastDual57_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,10]
def points : Finset C13.Point := {2,6,7,10}
def columns : List Code := [379,439,631,699,823,827,829,830,859,875,883,923,939,947,971,979,995,1339,1371,1402,1447,1453,1461,1595,1639,1646,1654,1691,1721,1819,1831,1843,1882,1894,1906,1945,1957,1969,2363,2395,2411,2425,2455,2462,2486,2619,2647,2653,2677,2715,2731,2746,2839,2843,2845,2846,2859,2867,2869,2870,2873,2874,2876,2891,2899,2901,2905,2915,2921,2929,2955,2963,2966,2970,2979,2986,2994,3011,3131,3277,3278,3292,3308,3355,3379,3418,3469,3493,3532,3611,3635,3662,3686,3737,3788]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 2055,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 197,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 86,1,1⟩,⟨.covers 166,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 2224,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 3152,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 3616,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source57.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source57.rootCodes link57 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual57_008
namespace C13.Global.FastDual57_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,11]
def points : Finset C13.Point := {2,6,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,859,875,883,923,939,947,971,979,995,1339,1371,1387,1402,1447,1453,1461,1595,1639,1646,1654,1691,1707,1721,1819,1831,1835,1837,1838,1843,1845,1846,1849,1850,1852,1867,1875,1882,1891,1894,1898,1906,1931,1939,1945,1955,1957,1961,1969,1987,2363,2411,2425,2455,2462,2486,2619,2647,2653,2677,2731,2746,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3277,3278,3292,3308,3371,3379,3433,3470,3478,3532,3627,3635,3661,3669,3754,3788]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 135,1,1⟩,⟨.covers 1031,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 86,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 540,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 2224,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 3616,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 1856,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source57.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source57.rootCodes link57 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual57_009
