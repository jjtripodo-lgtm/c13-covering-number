import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source52
namespace C13.Global.FastDual52_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,5,6]
def points : Finset C13.Point := {1,2,5,6}
def columns : List Code := [445,475,829,956,971,979,1371,1453,1461,1498,1639,1646,1654,1766,1837,1845,1852,1867,1875,1882,1894,1945,1957,1964,1972,1987,1994,2002,2235,2269,2425,2455,2459,2461,2462,2489,2521,2537,2653,2731,2746,2773,2845,2873,2876,2901,2905,2921,2955,2963,2965,2966,2969,2970,2972,2985,2986,3000,3011,3017,3025,3131,3251,3277,3292,3355,3379,3385,3417,3418,3433,3469,3475,3477,3478,3481,3482,3484,3493,3497,3505,3529,3532,3544,3627,3635,3642,3661,3669,3676,3686,3737,3747,3754,3762,3781,3788,3796,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 39,1,19⟩,⟨.covers 135,1,19⟩,⟨.covers 43,1,3⟩,⟨.covers 75,1,1⟩,⟨.covers 523,1,6⟩,⟨.covers 1035,1,6⟩,⟨.covers 83,1,10⟩,⟨.covers 163,1,6⟩,⟨.covers 1283,1,2⟩,⟨.covers 2563,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 77,1,3⟩,⟨.covers 525,1,2⟩,⟨.covers 1037,1,9⟩,⟨.covers 53,1,10⟩,⟨.covers 197,1,5⟩,⟨.covers 773,1,1⟩,⟨.covers 3077,1,2⟩,⟨.covers 3105,1,2⟩,⟨.covers 833,1,1⟩,⟨.covers 2625,1,3⟩,⟨.covers 1665,1,9⟩,⟨.covers 46,1,19⟩,⟨.covers 142,1,19⟩,⟨.covers 54,1,19⟩,⟨.covers 166,1,19⟩,⟨.covers 1286,1,4⟩,⟨.covers 2566,1,9⟩,⟨.covers 58,1,7⟩,⟨.covers 202,1,8⟩,⟨.covers 178,1,3⟩,⟨.covers 3090,1,2⟩,⟨.covers 834,1,4⟩,⟨.covers 2690,1,2⟩,⟨.covers 92,1,6⟩,⟨.covers 172,1,9⟩,⟨.covers 1292,1,1⟩,⟨.covers 212,1,4⟩,⟨.covers 2580,1,4⟩,⟨.covers 804,1,5⟩,⟨.covers 120,1,19⟩,⟨.covers 1560,1,9⟩,⟨.covers 232,1,19⟩,⟨.covers 808,1,1⟩,⟨.covers 2600,1,1⟩,⟨.covers 1672,1,2⟩,⟨.covers 3336,1,4⟩,⟨.covers 688,1,5⟩,⟨.covers 1200,1,6⟩,⟨.covers 1328,1,3⟩,⟨.covers 2608,1,1⟩,⟨.covers 720,1,2⟩,⟨.covers 1232,1,9⟩,⟨.covers 848,1,2⟩,⟨.covers 864,1,6⟩,⟨.covers 2656,1,7⟩,⟨.covers 1472,1,2⟩,⟨.covers 2944,1,4⟩]
def bound : Int := 20

theorem column_mask : listMask columns = restrictMask universeMask Source52.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source52.rootCodes link52 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual52_000
namespace C13.Global.FastDual52_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,5,9]
def points : Finset C13.Point := {1,2,5,9}
def columns : List Code := [445,475,829,892,956,971,979,985,1371,1453,1461,1491,1497,1498,1509,1639,1646,1654,1753,1766,1852,1894,1908,1945,1987,2001,2235,2269,2425,2455,2459,2461,2462,2489,2515,2517,2518,2521,2522,2524,2537,2653,2731,2746,2773,2777,2794,2845,2876,2901,2955,2969,2986,3000,3011,3025,3131,3187,3251,3277,3285,3289,3292,3355,3379,3385,3411,3417,3418,3433,3441,3469,3475,3477,3478,3481,3482,3484,3493,3497,3505,3525,3529,3532,3537,3538,3540,3544,3553,3669,3686,3737,3754,3793,3810]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 135,1,1⟩,⟨.covers 523,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 54,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 58,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 2272,1,1⟩,⟨.covers 928,1,1⟩,⟨.covers 2880,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source52.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source52.rootCodes link52 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual52_001
namespace C13.Global.FastDual52_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,5,10]
def points : Finset C13.Point := {1,2,5,10}
def columns : List Code := [445,475,829,892,956,971,979,985,986,1371,1453,1461,1497,1498,1509,1639,1646,1654,1753,1766,1882,1894,1945,1957,2008,2020,2235,2269,2425,2455,2459,2461,2462,2489,2515,2517,2518,2521,2522,2524,2537,2653,2731,2746,2773,2777,2780,2794,2845,2873,2876,2901,2905,2908,2921,2936,2955,2963,2965,2966,2969,2970,2972,2985,2986,3000,3011,3017,3018,3025,3026,3028,3032,3048,3131,3187,3251,3277,3289,3292,3355,3379,3418,3469,3481,3493,3505,3532,3544,3635,3686,3698,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 135,1,1⟩,⟨.covers 43,1,1⟩,⟨.covers 1283,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 2145,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 54,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 58,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 688,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 2848,1,1⟩,⟨.covers 3392,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source52.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source52.rootCodes link52 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual52_002
namespace C13.Global.FastDual52_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,5,11]
def points : Finset C13.Point := {1,2,5,11}
def columns : List Code := [445,475,829,892,956,971,979,985,986,1371,1453,1461,1491,1497,1498,1509,1639,1646,1654,1753,1766,1837,1845,1852,1867,1875,1881,1882,1893,1894,1900,1908,1945,1957,1964,1972,1987,1993,1994,2001,2002,2008,2020,2235,2269,2425,2455,2462,2517,2518,2524,2537,2653,2731,2746,2773,2780,2794,2901,2921,2966,2986,3028,3048,3131,3187,3251,3277,3285,3292,3379,3433,3441,3478,3532,3540,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 39,1,15⟩,⟨.covers 135,1,18⟩,⟨.covers 83,1,5⟩,⟨.covers 99,1,3⟩,⟨.covers 163,1,10⟩,⟨.covers 643,1,2⟩,⟨.covers 1283,1,5⟩,⟨.covers 2563,1,2⟩,⟨.covers 53,1,1⟩,⟨.covers 197,1,3⟩,⟨.covers 773,1,4⟩,⟨.covers 3077,1,2⟩,⟨.covers 1185,1,2⟩,⟨.covers 705,1,3⟩,⟨.covers 46,1,8⟩,⟨.covers 142,1,18⟩,⟨.covers 86,1,13⟩,⟨.covers 166,1,16⟩,⟨.covers 774,1,4⟩,⟨.covers 1286,1,9⟩,⟨.covers 2566,1,5⟩,⟨.covers 1050,1,2⟩,⟨.covers 106,1,9⟩,⟨.covers 202,1,5⟩,⟨.covers 778,1,5⟩,⟨.covers 3082,1,12⟩,⟨.covers 114,1,5⟩,⟨.covers 210,1,5⟩,⟨.covers 1794,1,5⟩,⟨.covers 2818,1,7⟩,⟨.covers 3330,1,9⟩,⟨.covers 92,1,3⟩,⟨.covers 540,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 1164,1,2⟩,⟨.covers 1292,1,2⟩,⟨.covers 2572,1,2⟩,⟨.covers 180,1,3⟩,⟨.covers 228,1,1⟩,⟨.covers 2820,1,2⟩,⟨.covers 3588,1,3⟩,⟨.covers 120,1,2⟩,⟨.covers 184,1,2⟩,⟨.covers 1304,1,3⟩,⟨.covers 3336,1,3⟩,⟨.covers 1328,1,1⟩,⟨.covers 2608,1,12⟩,⟨.covers 3152,1,2⟩,⟨.covers 2464,1,3⟩,⟨.covers 3232,1,2⟩,⟨.incident 1,8,-11⟩,⟨.incident 2,8,-4⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source52.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source52.rootCodes link52 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual52_003
namespace C13.Global.FastDual52_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,7,11]
def points : Finset C13.Point := {1,2,7,11}
def columns : List Code := [637,747,829,885,889,892,971,979,995,1147,1261,1371,1395,1401,1402,1453,1461,1509,1639,1643,1645,1646,1651,1653,1654,1657,1658,1660,1721,1753,1769,1837,1845,1849,1852,1867,1875,1881,1882,1891,1893,1894,1897,1898,1900,1905,1906,1908,1912,1945,1957,1961,1969,1987,1993,2001,2017,2425,2455,2462,2486,2518,2653,2677,2681,2731,2746,2794,2901,2921,2929,2966,2986,2994,3131,3187,3193,3277,3292,3308,3379,3433,3441,3478,3532,3540,3627,3635,3661,3669,3689,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 135,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 166,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 2880,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source52.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source52.rootCodes link52 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual52_004
