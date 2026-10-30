import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source40
namespace C13.Global.FastDual40_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,3,6]
def points : Finset C13.Point := {1,2,3,6}
def columns : List Code := [254,506,758,829,949,953,956,979,995,1010,1371,1402,1461,1498,1639,1654,1721,1766,1845,1849,1852,1875,1882,1891,1894,1906,1945,1957,1969,1972,1976,1987,2002,2018,2300,2425,2455,2483,2485,2486,2537,2552,2677,2731,2739,2745,2746,2773,2804,2869,2873,2876,2901,2921,2929,2963,2965,2966,2979,2985,2986,2993,2994,2996,3000,3011,3025,3041,3056,3251,3277,3292,3308,3379,3417,3418,3433,3448,3475,3477,3478,3493,3505,3506,3508,3529,3532,3544,3560,3635,3669,3685,3686,3700,3737,3747,3753,3754,3761,3762,3768,3781,3788,3796,3812,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 135,1,3⟩,⟨.covers 263,1,1⟩,⟨.covers 519,1,3⟩,⟨.covers 75,1,3⟩,⟨.covers 139,1,4⟩,⟨.covers 77,1,3⟩,⟨.covers 269,1,4⟩,⟨.covers 593,1,1⟩,⟨.covers 2129,1,1⟩,⟨.covers 353,1,1⟩,⟨.covers 2145,1,1⟩,⟨.covers 449,1,1⟩,⟨.covers 705,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 1074,1,1⟩,⟨.covers 2098,1,2⟩,⟨.covers 3090,1,2⟩,⟨.covers 3106,1,2⟩,⟨.covers 898,1,1⟩,⟨.covers 2580,1,1⟩,⟨.covers 420,1,2⟩,⟨.covers 1188,1,1⟩,⟨.covers 1316,1,2⟩,⟨.covers 1412,1,2⟩,⟨.covers 664,1,2⟩,⟨.covers 1176,1,1⟩,⟨.covers 1560,1,2⟩,⟨.covers 2344,1,1⟩,⟨.covers 1672,1,2⟩,⟨.covers 368,1,1⟩,⟨.covers 624,1,1⟩,⟨.covers 464,1,1⟩,⟨.covers 2256,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 3152,1,1⟩,⟨.covers 736,1,1⟩,⟨.covers 2272,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 2880,1,2⟩,⟨.incident 1,8,3⟩,⟨.incident 2,8,3⟩,⟨.incident 3,8,3⟩,⟨.incident 6,8,1⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_000
namespace C13.Global.FastDual40_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,3,8]
def points : Finset C13.Point := {1,2,3,8}
def columns : List Code := [247,251,253,254,499,501,502,505,506,508,755,757,758,761,762,764,829,889,892,949,956,979,995,1009,1010,1012,1016,1267,1269,1270,1273,1274,1276,1371,1401,1402,1461,1491,1498,1509,1521,1522,1524,1528,1639,1651,1653,1654,1721,1753,1763,1765,1766,1777,1778,1780,1784,1852,1882,1912,1957,1972,1987,2002,2017,2032,2291,2293,2294,2297,2298,2300,2425,2455,2485,2486,2515,2518,2537,2545,2546,2548,2552,2677,2731,2739,2745,2746,2773,2787,2793,2794,2801,2802,2804,2808,2876,2921,2936,2966,2996,3011,3026,3041,3056,3187,3251,3277,3285,3289,3292,3301,3305,3308,3313,3314,3316,3320,3418,3433,3448,3478,3493,3508,3538,3553,3568,3635,3669,3683,3685,3686,3697,3698,3700,3737,3747,3753,3754,3761,3762,3768,3781,3785,3788,3793,3796,3800,3809,3810,3812,3816,3824,3854,3884,3914,3944,3974,4004,4034,4064]
def rows : List LinearRow := [⟨.covers 135,1,3⟩,⟨.covers 519,1,4⟩,⟨.covers 75,1,3⟩,⟨.covers 139,1,1⟩,⟨.covers 523,1,3⟩,⟨.covers 77,1,4⟩,⟨.covers 269,1,3⟩,⟨.covers 1313,1,1⟩,⟨.covers 2337,1,1⟩,⟨.covers 833,1,1⟩,⟨.covers 2369,1,1⟩,⟨.covers 897,1,1⟩,⟨.covers 1409,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 1074,1,2⟩,⟨.covers 2098,1,2⟩,⟨.covers 3090,1,1⟩,⟨.covers 3106,1,2⟩,⟨.covers 706,1,1⟩,⟨.covers 596,1,2⟩,⟨.covers 2132,1,2⟩,⟨.covers 2580,1,1⟩,⟨.covers 1188,1,1⟩,⟨.covers 2628,1,2⟩,⟨.covers 664,1,2⟩,⟨.covers 1176,1,2⟩,⟨.covers 1560,1,1⟩,⟨.covers 2152,1,1⟩,⟨.covers 1672,1,2⟩,⟨.covers 1328,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 848,1,1⟩,⟨.covers 2384,1,1⟩,⟨.covers 912,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 480,1,2⟩,⟨.covers 1824,1,1⟩,⟨.covers 2848,1,1⟩,⟨.covers 1856,1,1⟩,⟨.covers 3392,1,1⟩,⟨.covers 2944,1,1⟩,⟨.covers 3456,1,1⟩,⟨.incident 1,8,3⟩,⟨.incident 2,8,3⟩,⟨.incident 3,8,3⟩,⟨.incident 8,8,1⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_001
namespace C13.Global.FastDual40_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,6,8]
def points : Finset C13.Point := {1,2,6,8}
def columns : List Code := [254,445,475,506,758,829,949,956,971,979,995,1010,1371,1402,1453,1461,1468,1498,1639,1646,1654,1721,1766,1837,1852,1867,1882,1957,1972,1987,2002,2235,2269,2300,2425,2455,2462,2485,2486,2492,2537,2552,2653,2677,2731,2739,2745,2746,2773,2804,2876,2921,2966,2996,3011,3041,3056,3131,3251,3257,3258,3277,3292,3308,3418,3433,3448,3478,3493,3508,3627,3635,3641,3642,3661,3669,3676,3685,3686,3692,3700,3737,3747,3753,3754,3761,3762,3768,3781,3788,3796,3812,3854,3884,3914,3944,3974,4004,4034,4064]
def rows : List LinearRow := [⟨.covers 71,1,30⟩,⟨.covers 135,1,32⟩,⟨.covers 139,1,16⟩,⟨.covers 523,1,18⟩,⟨.covers 2059,1,14⟩,⟨.covers 83,1,13⟩,⟨.covers 163,1,14⟩,⟨.covers 1283,1,16⟩,⟨.covers 2563,1,14⟩,⟨.covers 77,1,29⟩,⟨.covers 141,1,2⟩,⟨.covers 269,1,30⟩,⟨.covers 197,1,10⟩,⟨.covers 773,1,14⟩,⟨.covers 3077,1,4⟩,⟨.covers 593,1,14⟩,⟨.covers 353,1,11⟩,⟨.covers 2145,1,10⟩,⟨.covers 417,1,9⟩,⟨.covers 2337,1,8⟩,⟨.covers 2369,1,19⟩,⟨.covers 2625,1,1⟩,⟨.covers 1409,1,12⟩,⟨.covers 142,1,1⟩,⟨.covers 270,1,18⟩,⟨.covers 198,1,5⟩,⟨.covers 774,1,11⟩,⟨.covers 282,1,4⟩,⟨.covers 2098,1,32⟩,⟨.covers 3106,1,30⟩,⟨.covers 284,1,8⟩,⟨.covers 108,1,15⟩,⟨.covers 1100,1,15⟩,⟨.covers 788,1,2⟩,⟨.covers 2580,1,17⟩,⟨.covers 228,1,6⟩,⟨.covers 1188,1,10⟩,⟨.covers 664,1,44⟩,⟨.covers 1176,1,12⟩,⟨.covers 792,1,8⟩,⟨.covers 1560,1,4⟩,⟨.covers 232,1,3⟩,⟨.covers 2344,1,6⟩,⟨.covers 1672,1,46⟩,⟨.covers 2824,1,3⟩,⟨.covers 368,1,4⟩,⟨.covers 624,1,20⟩,⟨.covers 1328,1,21⟩,⟨.covers 2256,1,20⟩,⟨.covers 848,1,6⟩,⟨.covers 2384,1,8⟩,⟨.covers 1616,1,11⟩,⟨.covers 3152,1,14⟩,⟨.covers 1424,1,11⟩,⟨.covers 1376,1,4⟩,⟨.covers 1824,1,19⟩,⟨.covers 2848,1,8⟩,⟨.covers 1472,1,6⟩,⟨.covers 3392,1,7⟩,⟨.covers 3456,1,21⟩,⟨.incident 1,8,31⟩,⟨.incident 2,8,24⟩,⟨.incident 6,8,22⟩,⟨.incident 8,8,20⟩]
def bound : Int := 109

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_002
namespace C13.Global.FastDual40_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,6,9]
def points : Finset C13.Point := {1,2,6,9}
def columns : List Code := [254,445,475,506,758,829,953,956,971,979,995,1010,1371,1402,1453,1461,1465,1468,1498,1639,1646,1654,1721,1766,1852,1894,1945,1976,1987,2018,2235,2269,2300,2425,2455,2459,2461,2462,2483,2485,2486,2489,2490,2492,2521,2537,2552,2653,2677,2731,2745,2746,2773,2804,2845,2876,2901,2955,2969,2986,3000,3011,3025,3056,3131,3251,3257,3258,3277,3292,3308,3355,3379,3385,3386,3417,3418,3433,3448,3469,3475,3477,3478,3481,3482,3484,3493,3497,3500,3505,3506,3508,3512,3529,3532,3544,3560,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 135,1,2⟩,⟨.covers 83,1,2⟩,⟨.covers 99,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 2083,1,1⟩,⟨.covers 270,1,2⟩,⟨.covers 526,1,2⟩,⟨.covers 86,1,2⟩,⟨.covers 774,1,2⟩,⟨.covers 3078,1,1⟩,⟨.covers 778,1,2⟩,⟨.covers 3082,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 1728,1,2⟩,⟨.incident 1,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_003
namespace C13.Global.FastDual40_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,6,11]
def points : Finset C13.Point := {1,2,6,11}
def columns : List Code := [254,445,475,506,758,829,949,953,956,971,979,995,1010,1371,1402,1453,1461,1465,1468,1498,1639,1646,1654,1721,1766,1837,1845,1849,1852,1867,1875,1882,1891,1894,1898,1906,1945,1957,1961,1964,1969,1972,1976,1987,1994,2002,2018,2235,2269,2300,2425,2455,2462,2483,2486,2490,2537,2552,2653,2677,2731,2739,2746,2773,2804,2901,2921,2929,2966,2986,2994,3056,3131,3251,3258,3277,3292,3308,3379,3433,3478,3506,3532,3560,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 135,1,3⟩,⟨.covers 269,1,1⟩,⟨.covers 197,1,3⟩,⟨.covers 773,1,1⟩,⟨.covers 526,1,3⟩,⟨.covers 1286,1,2⟩,⟨.covers 2566,1,1⟩,⟨.covers 2316,1,2⟩,⟨.covers 2572,1,3⟩,⟨.covers 116,1,3⟩,⟨.covers 308,1,1⟩,⟨.covers 1188,1,1⟩,⟨.covers 2820,1,2⟩,⟨.covers 3152,1,3⟩,⟨.incident 2,8,-3⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_004
namespace C13.Global.FastDual40_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,7,8]
def points : Finset C13.Point := {1,2,7,8}
def columns : List Code := [637,747,829,889,892,971,979,995,1147,1261,1371,1401,1402,1453,1461,1509,1639,1643,1645,1646,1651,1653,1654,1657,1658,1660,1721,1753,1769,1837,1852,1867,1882,1897,1912,1957,1987,2017,2425,2455,2462,2486,2518,2653,2677,2681,2684,2731,2746,2794,2876,2921,2936,2966,3011,3026,3131,3187,3193,3194,3277,3292,3308,3418,3433,3448,3478,3493,3508,3627,3635,3641,3642,3661,3669,3673,3676,3683,3685,3686,3689,3690,3692,3697,3698,3700,3704,3737,3753,3754,3768,3785,3788,3800,3816,3854,3884,3914,3944,3974,4004,4034,4064]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 135,1,2⟩,⟨.covers 269,1,2⟩,⟨.covers 2061,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 78,1,2⟩,⟨.covers 142,1,2⟩,⟨.covers 166,1,2⟩,⟨.covers 198,1,2⟩,⟨.covers 774,1,2⟩,⟨.covers 116,1,1⟩,⟨.covers 228,1,2⟩,⟨.covers 1424,1,2⟩,⟨.incident 2,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_005
namespace C13.Global.FastDual40_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,7,9]
def points : Finset C13.Point := {1,2,7,9}
def columns : List Code := [637,747,829,885,892,971,979,995,1147,1261,1371,1395,1401,1402,1453,1461,1509,1639,1646,1653,1654,1660,1721,1753,1852,1894,1908,1945,1987,2001,2425,2455,2462,2486,2518,2653,2677,2684,2731,2746,2794,2845,2876,2901,2932,2955,2986,3011,3042,3131,3187,3193,3194,3277,3292,3308,3355,3379,3385,3386,3411,3417,3418,3433,3441,3442,3448,3469,3477,3478,3484,3493,3500,3508,3525,3532,3540,3556,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,2⟩,⟨.covers 83,1,1⟩,⟨.covers 1539,1,2⟩,⟨.covers 2563,1,2⟩,⟨.covers 78,1,2⟩,⟨.covers 142,1,2⟩,⟨.covers 86,1,1⟩,⟨.covers 774,1,2⟩,⟨.covers 2566,1,1⟩,⟨.covers 202,1,2⟩,⟨.covers 3082,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 178,1,2⟩,⟨.covers 210,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 928,1,2⟩,⟨.incident 1,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_006
namespace C13.Global.FastDual40_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,7,11]
def points : Finset C13.Point := {1,2,7,11}
def columns : List Code := [637,747,829,885,889,892,971,979,995,1147,1261,1371,1395,1401,1402,1453,1461,1509,1639,1643,1645,1646,1651,1653,1654,1657,1658,1660,1721,1753,1769,1837,1845,1849,1852,1867,1875,1881,1882,1891,1893,1894,1897,1898,1900,1905,1906,1908,1912,1945,1957,1961,1969,1987,1993,2001,2017,2425,2455,2462,2486,2518,2653,2677,2681,2731,2746,2794,2901,2921,2929,2966,2986,2994,3131,3187,3193,3277,3292,3308,3379,3433,3441,3478,3532,3540,3627,3635,3661,3669,3689,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 71,1,11⟩,⟨.covers 139,1,8⟩,⟨.covers 267,1,2⟩,⟨.covers 1043,1,2⟩,⟨.covers 163,1,3⟩,⟨.covers 1283,1,3⟩,⟨.covers 2307,1,3⟩,⟨.covers 269,1,6⟩,⟨.covers 2061,1,5⟩,⟨.covers 149,1,5⟩,⟨.covers 533,1,1⟩,⟨.covers 773,1,2⟩,⟨.covers 2309,1,3⟩,⟨.covers 3077,1,7⟩,⟨.covers 78,1,11⟩,⟨.covers 142,1,11⟩,⟨.covers 86,1,6⟩,⟨.covers 166,1,11⟩,⟨.covers 198,1,6⟩,⟨.covers 1286,1,3⟩,⟨.covers 2566,1,11⟩,⟨.covers 3078,1,9⟩,⟨.covers 1050,1,3⟩,⟨.covers 778,1,1⟩,⟨.covers 3082,1,6⟩,⟨.covers 114,1,1⟩,⟨.covers 1794,1,6⟩,⟨.covers 3586,1,5⟩,⟨.covers 92,1,5⟩,⟨.covers 172,1,5⟩,⟨.covers 116,1,3⟩,⟨.covers 228,1,6⟩,⟨.covers 1796,1,3⟩,⟨.covers 120,1,1⟩,⟨.covers 184,1,10⟩,⟨.covers 312,1,2⟩,⟨.covers 216,1,3⟩,⟨.covers 1304,1,2⟩,⟨.covers 2824,1,6⟩,⟨.covers 3336,1,11⟩,⟨.covers 2160,1,5⟩,⟨.covers 1328,1,3⟩,⟨.covers 1584,1,2⟩,⟨.covers 2608,1,2⟩,⟨.covers 720,1,8⟩,⟨.covers 3152,1,3⟩,⟨.covers 480,1,5⟩,⟨.covers 928,1,3⟩,⟨.covers 2752,1,11⟩,⟨.covers 2880,1,5⟩,⟨.covers 1920,1,3⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_007
