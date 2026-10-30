import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source42
namespace C13.Global.FastDual42_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,3,6]
def points : Finset C13.Point := {1,2,3,6}
def columns : List Code := [254,506,758,829,949,953,956,979,995,1010,1371,1402,1461,1498,1639,1654,1721,1766,1845,1849,1852,1875,1882,1891,1894,1906,1945,1957,1969,1972,1976,1987,2002,2018,2300,2425,2455,2483,2485,2486,2537,2552,2677,2731,2739,2745,2746,2773,2804,2869,2873,2876,2901,2921,2929,2963,2965,2966,2979,2985,2986,2993,2994,2996,3000,3011,3025,3041,3056,3251,3277,3292,3308,3379,3417,3418,3433,3448,3475,3477,3478,3493,3505,3506,3508,3529,3532,3544,3560,3635,3669,3685,3686,3700,3737,3747,3753,3754,3761,3762,3768,3781,3788,3796,3812,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 135,1,3⟩,⟨.covers 263,1,1⟩,⟨.covers 519,1,3⟩,⟨.covers 75,1,3⟩,⟨.covers 139,1,4⟩,⟨.covers 77,1,3⟩,⟨.covers 269,1,4⟩,⟨.covers 593,1,1⟩,⟨.covers 2129,1,1⟩,⟨.covers 353,1,1⟩,⟨.covers 2145,1,1⟩,⟨.covers 449,1,1⟩,⟨.covers 705,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 1074,1,1⟩,⟨.covers 2098,1,2⟩,⟨.covers 3090,1,2⟩,⟨.covers 3106,1,2⟩,⟨.covers 898,1,1⟩,⟨.covers 2580,1,1⟩,⟨.covers 420,1,2⟩,⟨.covers 1188,1,1⟩,⟨.covers 1316,1,2⟩,⟨.covers 1412,1,2⟩,⟨.covers 664,1,2⟩,⟨.covers 1176,1,1⟩,⟨.covers 1560,1,2⟩,⟨.covers 2344,1,1⟩,⟨.covers 1672,1,2⟩,⟨.covers 368,1,1⟩,⟨.covers 624,1,1⟩,⟨.covers 464,1,1⟩,⟨.covers 2256,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 3152,1,1⟩,⟨.covers 736,1,1⟩,⟨.covers 2272,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 2880,1,2⟩,⟨.incident 1,8,3⟩,⟨.incident 2,8,3⟩,⟨.incident 3,8,3⟩,⟨.incident 6,8,1⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source42.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source42.rootCodes link42 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual42_000
namespace C13.Global.FastDual42_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,3,11]
def points : Finset C13.Point := {1,2,3,11}
def columns : List Code := [247,251,253,254,499,501,502,505,506,508,755,757,758,761,762,764,829,885,889,892,949,953,956,979,995,1009,1010,1012,1016,1267,1269,1270,1273,1274,1276,1371,1395,1401,1402,1461,1491,1497,1498,1509,1521,1522,1524,1528,1639,1651,1653,1654,1721,1753,1763,1765,1766,1777,1778,1780,1784,1845,1849,1852,1875,1881,1882,1891,1893,1894,1905,1906,1908,1912,1945,1957,1969,1972,1976,1987,2001,2002,2008,2017,2018,2020,2032,2291,2293,2294,2297,2298,2300,2425,2455,2483,2486,2517,2518,2537,2545,2546,2548,2552,2677,2731,2739,2746,2773,2793,2794,2801,2802,2804,2808,2901,2921,2929,2966,2986,2994,3028,3048,3056,3187,3251,3277,3285,3292,3305,3308,3313,3314,3316,3320,3379,3433,3441,3478,3506,3532,3540,3560,3568,3635,3669,3697,3754,3762,3788,3796,3816,3824,3854,3862,3882,3890,3916,3924,3944,3952]
def rows : List LinearRow := [⟨.covers 263,1,3⟩,⟨.covers 519,1,4⟩,⟨.covers 75,1,4⟩,⟨.covers 523,1,3⟩,⟨.covers 77,1,3⟩,⟨.covers 269,1,4⟩,⟨.covers 2577,1,1⟩,⟨.covers 3089,1,1⟩,⟨.covers 2337,1,1⟩,⟨.covers 3105,1,1⟩,⟨.covers 2369,1,1⟩,⟨.covers 2625,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 1074,1,1⟩,⟨.covers 450,1,2⟩,⟨.covers 706,1,2⟩,⟨.covers 834,1,2⟩,⟨.covers 898,1,1⟩,⟨.covers 596,1,1⟩,⟨.covers 420,1,2⟩,⟨.covers 1188,1,2⟩,⟨.covers 1316,1,2⟩,⟨.covers 1412,1,1⟩,⟨.covers 664,1,2⟩,⟨.covers 1176,1,2⟩,⟨.covers 1560,1,2⟩,⟨.covers 360,1,1⟩,⟨.covers 1672,1,1⟩,⟨.covers 2160,1,2⟩,⟨.covers 2704,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 2832,1,1⟩,⟨.covers 3344,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 2848,1,1⟩,⟨.covers 3616,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 3392,1,1⟩,⟨.covers 3648,1,1⟩,⟨.incident 1,8,3⟩,⟨.incident 2,8,3⟩,⟨.incident 3,8,3⟩,⟨.incident 11,8,1⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source42.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source42.rootCodes link42 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual42_001
namespace C13.Global.FastDual42_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,6,8]
def points : Finset C13.Point := {1,2,6,8}
def columns : List Code := [254,445,475,506,758,829,949,956,971,979,995,1010,1371,1402,1453,1461,1468,1498,1639,1646,1654,1721,1766,1837,1852,1867,1882,1957,1972,1987,2002,2235,2269,2300,2425,2455,2462,2485,2486,2492,2537,2552,2653,2677,2731,2739,2745,2746,2773,2804,2876,2921,2966,2996,3011,3041,3056,3131,3251,3257,3258,3277,3292,3308,3418,3433,3448,3478,3493,3508,3627,3635,3641,3642,3661,3669,3676,3685,3686,3692,3700,3737,3747,3753,3754,3761,3762,3768,3781,3788,3796,3812]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 2059,1,1⟩,⟨.covers 83,1,2⟩,⟨.covers 163,1,1⟩,⟨.covers 2307,1,2⟩,⟨.covers 526,1,2⟩,⟨.covers 86,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 774,1,2⟩,⟨.covers 1286,1,2⟩,⟨.covers 778,1,2⟩,⟨.covers 2314,1,2⟩,⟨.covers 1074,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 1472,1,2⟩,⟨.incident 1,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source42.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source42.rootCodes link42 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual42_002
namespace C13.Global.FastDual42_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,6,9]
def points : Finset C13.Point := {1,2,6,9}
def columns : List Code := [254,445,475,506,758,829,953,956,971,979,995,1010,1371,1402,1453,1461,1465,1468,1498,1639,1646,1654,1721,1766,1852,1894,1945,1976,1987,2018,2235,2269,2300,2425,2455,2459,2461,2462,2483,2485,2486,2489,2490,2492,2521,2537,2552,2653,2677,2731,2745,2746,2773,2804,2845,2876,2901,2955,2969,2986,3000,3011,3025,3056,3131,3251,3257,3258,3277,3292,3308,3355,3379,3385,3386,3417,3418,3433,3448,3469,3475,3477,3478,3481,3482,3484,3493,3497,3500,3505,3506,3508,3512,3529,3532,3544,3560,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 135,1,2⟩,⟨.covers 83,1,2⟩,⟨.covers 99,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 2083,1,1⟩,⟨.covers 270,1,2⟩,⟨.covers 526,1,2⟩,⟨.covers 86,1,2⟩,⟨.covers 774,1,2⟩,⟨.covers 3078,1,1⟩,⟨.covers 778,1,2⟩,⟨.covers 3082,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 1728,1,2⟩,⟨.incident 1,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source42.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source42.rootCodes link42 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual42_003
namespace C13.Global.FastDual42_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,6,11]
def points : Finset C13.Point := {1,2,6,11}
def columns : List Code := [254,445,475,506,758,829,949,953,956,971,979,995,1010,1371,1402,1453,1461,1465,1468,1498,1639,1646,1654,1721,1766,1837,1845,1849,1852,1867,1875,1882,1891,1894,1898,1906,1945,1957,1961,1964,1969,1972,1976,1987,1994,2002,2018,2235,2269,2300,2425,2455,2462,2483,2486,2490,2537,2552,2653,2677,2731,2739,2746,2773,2804,2901,2921,2929,2966,2986,2994,3056,3131,3251,3258,3277,3292,3308,3379,3433,3478,3506,3532,3560,3627,3635,3661,3669,3754,3762,3788,3796,3854,3862,3882,3890,3916,3924,3944,3952]
def rows : List LinearRow := [⟨.covers 71,1,4⟩,⟨.covers 135,1,3⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,2⟩,⟨.covers 523,1,1⟩,⟨.covers 1035,1,2⟩,⟨.covers 83,1,2⟩,⟨.covers 1283,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 269,1,3⟩,⟨.covers 525,1,2⟩,⟨.covers 197,1,2⟩,⟨.covers 773,1,3⟩,⟨.covers 3089,1,2⟩,⟨.covers 353,1,1⟩,⟨.covers 2145,1,3⟩,⟨.covers 705,1,1⟩,⟨.covers 833,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 86,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 106,1,2⟩,⟨.covers 1098,1,1⟩,⟨.covers 1074,1,2⟩,⟨.covers 898,1,1⟩,⟨.covers 2690,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 284,1,2⟩,⟨.covers 420,1,3⟩,⟨.covers 1188,1,1⟩,⟨.covers 1316,1,2⟩,⟨.covers 1412,1,1⟩,⟨.covers 664,1,4⟩,⟨.covers 1176,1,1⟩,⟨.covers 1560,1,5⟩,⟨.covers 2344,1,1⟩,⟨.covers 1672,1,2⟩,⟨.covers 2696,1,1⟩,⟨.covers 368,1,1⟩,⟨.covers 464,1,2⟩,⟨.covers 3152,1,2⟩,⟨.covers 3216,1,1⟩,⟨.covers 3344,1,2⟩,⟨.covers 736,1,2⟩,⟨.covers 2272,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 3616,1,1⟩,⟨.covers 1472,1,3⟩,⟨.incident 1,8,3⟩,⟨.incident 2,8,3⟩,⟨.incident 6,8,3⟩,⟨.incident 11,8,3⟩]
def bound : Int := 13

theorem column_mask : listMask columns = restrictMask universeMask Source42.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source42.rootCodes link42 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual42_004
namespace C13.Global.FastDual42_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,8,11]
def points : Finset C13.Point := {1,2,8,11}
def columns : List Code := [247,251,253,254,445,475,499,501,502,505,506,508,637,747,755,757,758,761,762,764,829,889,892,949,956,971,979,986,995,1001,1009,1010,1012,1016,1147,1261,1267,1269,1270,1273,1274,1276,1371,1401,1402,1453,1461,1468,1491,1498,1509,1513,1521,1522,1524,1528,1639,1643,1645,1646,1651,1653,1654,1657,1658,1660,1721,1753,1763,1765,1766,1769,1770,1772,1777,1778,1780,1784,1837,1852,1867,1882,1897,1912,1957,1972,1987,2002,2017,2032,2235,2269,2291,2293,2294,2297,2298,2300,2425,2455,2462,2486,2518,2537,2545,2546,2548,2552,2653,2677,2681,2731,2739,2746,2773,2780,2793,2794,2801,2802,2804,2808,2921,2966,3056,3131,3187,3193,3251,3258,3277,3285,3292,3305,3308,3313,3314,3316,3320,3433,3478,3568,3627,3635,3661,3669,3689,3697,3754,3762,3788,3796,3816,3824]
def rows : List LinearRow := [⟨.covers 263,1,19⟩,⟨.covers 519,1,19⟩,⟨.covers 139,1,6⟩,⟨.covers 267,1,2⟩,⟨.covers 2059,1,6⟩,⟨.covers 83,1,2⟩,⟨.covers 1283,1,12⟩,⟨.covers 2563,1,1⟩,⟨.covers 141,1,6⟩,⟨.covers 269,1,6⟩,⟨.covers 2061,1,3⟩,⟨.covers 197,1,7⟩,⟨.covers 773,1,7⟩,⟨.covers 3077,1,1⟩,⟨.covers 2097,1,5⟩,⟨.covers 2129,1,1⟩,⟨.covers 657,1,9⟩,⟨.covers 417,1,2⟩,⟨.covers 449,1,1⟩,⟨.covers 270,1,19⟩,⟨.covers 526,1,19⟩,⟨.covers 86,1,7⟩,⟨.covers 166,1,4⟩,⟨.covers 774,1,19⟩,⟨.covers 1286,1,19⟩,⟨.covers 202,1,4⟩,⟨.covers 778,1,3⟩,⟨.covers 3082,1,7⟩,⟨.covers 1074,1,1⟩,⟨.covers 338,1,1⟩,⟨.covers 1106,1,1⟩,⟨.covers 674,1,3⟩,⟨.covers 2210,1,2⟩,⟨.covers 450,1,1⟩,⟨.covers 706,1,1⟩,⟨.covers 1794,1,2⟩,⟨.covers 3586,1,6⟩,⟨.covers 540,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 2572,1,13⟩,⟨.covers 308,1,2⟩,⟨.covers 2132,1,1⟩,⟨.covers 1188,1,5⟩,⟨.covers 1220,1,2⟩,⟨.covers 2244,1,1⟩,⟨.covers 1796,1,6⟩,⟨.covers 3588,1,3⟩,⟨.covers 120,1,4⟩,⟨.covers 312,1,3⟩,⟨.covers 344,1,1⟩,⟨.covers 664,1,2⟩,⟨.covers 1176,1,9⟩,⟨.covers 2696,1,1⟩,⟨.covers 2824,1,19⟩,⟨.covers 3336,1,19⟩,⟨.covers 2352,1,4⟩,⟨.covers 848,1,4⟩,⟨.covers 3152,1,6⟩,⟨.covers 1808,1,6⟩,⟨.covers 3600,1,7⟩,⟨.covers 736,1,4⟩,⟨.covers 2464,1,7⟩,⟨.covers 1472,1,2⟩]
def bound : Int := 20

theorem column_mask : listMask columns = restrictMask universeMask Source42.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source42.rootCodes link42 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual42_005
namespace C13.Global.FastDual42_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,8,9]
def points : Finset C13.Point := {1,6,8,9}
def columns : List Code := [254,445,475,506,701,743,758,829,956,967,971,979,995,1010,1150,1213,1341,1371,1374,1402,1453,1461,1468,1498,1597,1639,1646,1654,1693,1721,1724,1766,1852,1987,2173,2231,2235,2237,2238,2269,2285,2300,2365,2413,2425,2455,2462,2477,2485,2486,2492,2537,2552,2621,2653,2677,2717,2731,2734,2745,2746,2748,2773,2804,2876,3011,3056,3127,3131,3133,3134,3165,3181,3196,3229,3245,3251,3253,3254,3257,3258,3260,3277,3292,3308,3358,3373,3388,3418,3433,3448,3478,3493,3508,3613,3630,3644,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 2055,1,8⟩,⟨.covers 2059,1,8⟩,⟨.covers 83,1,13⟩,⟨.covers 99,1,13⟩,⟨.covers 269,1,8⟩,⟨.covers 525,1,9⟩,⟨.covers 1157,1,2⟩,⟨.covers 773,1,2⟩,⟨.covers 2309,1,5⟩,⟨.covers 1161,1,2⟩,⟨.covers 2569,1,5⟩,⟨.covers 270,1,13⟩,⟨.covers 526,1,13⟩,⟨.covers 774,1,17⟩,⟨.covers 778,1,19⟩,⟨.covers 114,1,7⟩,⟨.covers 1122,1,1⟩,⟨.covers 674,1,1⟩,⟨.covers 1794,1,19⟩,⟨.covers 2818,1,19⟩,⟨.covers 3586,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 1220,1,1⟩,⟨.covers 1796,1,19⟩,⟨.covers 2820,1,19⟩,⟨.covers 1224,1,2⟩,⟨.covers 720,1,5⟩,⟨.covers 2256,1,3⟩,⟨.covers 1616,1,2⟩,⟨.covers 1424,1,11⟩,⟨.covers 3216,1,2⟩,⟨.covers 2272,1,5⟩,⟨.covers 928,1,5⟩,⟨.covers 1696,1,12⟩,⟨.covers 3392,1,13⟩,⟨.covers 3648,1,12⟩,⟨.incident 8,8,-5⟩,⟨.incident 9,8,-6⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source42.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source42.rootCodes link42 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual42_006
namespace C13.Global.FastDual42_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,8,11]
def points : Finset C13.Point := {1,6,8,11}
def columns : List Code := [254,445,475,506,701,743,758,829,941,949,956,967,971,979,995,1010,1150,1213,1341,1371,1374,1402,1453,1461,1468,1498,1597,1639,1646,1654,1693,1709,1717,1721,1724,1766,1837,1852,1867,1882,1957,1972,1987,2002,2173,2231,2235,2238,2269,2285,2300,2413,2425,2455,2462,2486,2537,2552,2653,2669,2677,2731,2734,2739,2742,2746,2765,2773,2804,2921,2966,3056,3127,3131,3165,3181,3251,3254,3258,3277,3292,3308,3433,3478,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 263,1,8⟩,⟨.covers 83,1,25⟩,⟨.covers 269,1,8⟩,⟨.covers 773,1,8⟩,⟨.covers 2309,1,17⟩,⟨.covers 417,1,8⟩,⟨.covers 774,1,8⟩,⟨.covers 1286,1,25⟩,⟨.covers 778,1,25⟩,⟨.covers 2314,1,25⟩,⟨.covers 2818,1,17⟩,⟨.covers 308,1,8⟩,⟨.covers 1796,1,8⟩,⟨.covers 2824,1,25⟩,⟨.covers 3336,1,8⟩,⟨.covers 1328,1,8⟩,⟨.covers 2352,1,17⟩,⟨.covers 1376,1,17⟩,⟨.covers 1472,1,25⟩,⟨.covers 2496,1,8⟩,⟨.incident 8,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source42.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source42.rootCodes link42 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual42_007
