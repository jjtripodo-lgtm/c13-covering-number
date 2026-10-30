import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source50
namespace C13.Global.FastDual50_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,8]
def points : Finset C13.Point := {1,6,7,8}
def columns : List Code := [829,967,971,979,995,1150,1213,1341,1371,1374,1402,1453,1461,1597,1639,1646,1654,1693,1709,1721,1837,1852,1867,1882,1957,1987,2173,2238,2365,2413,2425,2455,2462,2486,2621,2653,2669,2677,2731,2734,2746,2861,2876,2921,2951,2966,3011,3127,3131,3133,3134,3165,3181,3196,3229,3245,3260,3277,3292,3308,3358,3373,3388,3418,3433,3448,3478,3493,3508,3613,3623,3627,3629,3630,3635,3637,3638,3641,3642,3644,3661,3669,3676,3685,3686,3692,3700,3725,3737,3740,3753,3754,3756,3768,3788]
def rows : List LinearRow := [⟨.covers 1031,1,8⟩,⟨.covers 1035,1,8⟩,⟨.covers 147,1,6⟩,⟨.covers 2067,1,3⟩,⟨.covers 163,1,8⟩,⟨.covers 77,1,6⟩,⟨.covers 141,1,6⟩,⟨.covers 269,1,3⟩,⟨.covers 149,1,3⟩,⟨.covers 101,1,3⟩,⟨.covers 89,1,3⟩,⟨.covers 169,1,3⟩,⟨.covers 1553,1,3⟩,⟨.covers 2577,1,3⟩,⟨.covers 3329,1,8⟩,⟨.covers 142,1,3⟩,⟨.covers 526,1,8⟩,⟨.covers 86,1,8⟩,⟨.covers 198,1,3⟩,⟨.covers 774,1,8⟩,⟨.covers 1286,1,3⟩,⟨.covers 154,1,8⟩,⟨.covers 106,1,3⟩,⟨.covers 202,1,11⟩,⟨.covers 1794,1,3⟩,⟨.covers 3330,1,8⟩,⟨.covers 3586,1,3⟩,⟨.covers 212,1,11⟩,⟨.covers 228,1,11⟩,⟨.covers 1796,1,8⟩,⟨.covers 2820,1,3⟩,⟨.covers 792,1,3⟩,⟨.covers 2824,1,6⟩,⟨.covers 368,1,8⟩,⟨.covers 624,1,3⟩,⟨.covers 432,1,8⟩,⟨.covers 688,1,3⟩,⟨.covers 848,1,6⟩,⟨.covers 864,1,3⟩,⟨.covers 2656,1,3⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,3⟩,⟨.covers 1472,1,8⟩,⟨.covers 2496,1,11⟩,⟨.covers 3392,1,3⟩,⟨.covers 3648,1,6⟩,⟨.covers 3712,1,6⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source50.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source50.rootCodes link50 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual50_008
namespace C13.Global.FastDual50_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,11]
def points : Finset C13.Point := {1,6,7,11}
def columns : List Code := [829,967,971,979,995,1150,1213,1341,1371,1374,1402,1437,1453,1461,1597,1639,1646,1654,1693,1709,1721,1821,1837,1845,1849,1852,1863,1867,1870,1875,1878,1882,1891,1894,1898,1906,1933,1941,1945,1957,1961,1969,1987,2173,2238,2397,2413,2425,2455,2462,2486,2653,2669,2677,2731,2734,2746,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3165,3181,3277,3292,3308,3351,3379,3405,3433,3478,3532,3627,3635,3661,3669,3754,3788]
def rows : List LinearRow := [⟨.covers 147,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 198,1,2⟩,⟨.covers 2566,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 202,1,2⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 212,1,2⟩,⟨.covers 228,1,2⟩,⟨.covers 2464,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 3712,1,1⟩,⟨.incident 6,8,-1⟩,⟨.incident 7,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source50.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source50.rootCodes link50 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual50_009
namespace C13.Global.FastDual50_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,8,9]
def points : Finset C13.Point := {1,6,8,9}
def columns : List Code := [254,445,475,506,701,743,758,829,956,967,971,979,995,1010,1150,1213,1341,1371,1374,1402,1453,1461,1468,1498,1597,1639,1646,1654,1693,1721,1724,1766,1852,1987,2173,2231,2235,2237,2238,2269,2285,2300,2365,2413,2425,2455,2462,2477,2485,2486,2492,2537,2552,2621,2653,2677,2717,2731,2734,2745,2746,2748,2773,2804,2876,3011,3056,3127,3131,3133,3134,3165,3181,3196,3229,3245,3251,3253,3254,3257,3258,3260,3277,3292,3308,3358,3373,3388,3418,3433,3448,3478,3493,3508,3613,3630,3644,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 2055,1,11⟩,⟨.covers 2059,1,11⟩,⟨.covers 83,1,10⟩,⟨.covers 99,1,14⟩,⟨.covers 269,1,8⟩,⟨.covers 525,1,8⟩,⟨.covers 1157,1,1⟩,⟨.covers 2309,1,3⟩,⟨.covers 89,1,3⟩,⟨.covers 1161,1,1⟩,⟨.covers 2569,1,3⟩,⟨.covers 657,1,3⟩,⟨.covers 2145,1,3⟩,⟨.covers 417,1,3⟩,⟨.covers 1793,1,12⟩,⟨.covers 2817,1,17⟩,⟨.covers 3329,1,3⟩,⟨.covers 3585,1,3⟩,⟨.covers 270,1,13⟩,⟨.covers 774,1,17⟩,⟨.covers 2566,1,14⟩,⟨.covers 106,1,10⟩,⟨.covers 1098,1,1⟩,⟨.covers 778,1,17⟩,⟨.covers 2314,1,1⟩,⟨.covers 2244,1,6⟩,⟨.covers 1796,1,17⟩,⟨.covers 2820,1,17⟩,⟨.covers 216,1,1⟩,⟨.covers 1224,1,3⟩,⟨.covers 624,1,3⟩,⟨.covers 2256,1,2⟩,⟨.covers 2384,1,6⟩,⟨.covers 1616,1,11⟩,⟨.covers 912,1,3⟩,⟨.covers 1424,1,10⟩,⟨.covers 2272,1,3⟩,⟨.covers 1376,1,3⟩,⟨.covers 1696,1,10⟩,⟨.covers 1728,1,4⟩,⟨.covers 3392,1,6⟩,⟨.covers 3456,1,4⟩,⟨.covers 3712,1,4⟩,⟨.incident 8,8,-3⟩,⟨.incident 9,8,-3⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source50.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source50.rootCodes link50 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual50_010
namespace C13.Global.FastDual50_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,8,9]
def points : Finset C13.Point := {1,7,8,9}
def columns : List Code := [381,471,637,747,829,892,967,971,979,995,1143,1147,1149,1150,1213,1245,1261,1341,1371,1374,1389,1401,1402,1404,1453,1461,1509,1597,1629,1639,1646,1653,1654,1660,1693,1721,1753,1852,1987,2173,2238,2365,2413,2425,2428,2455,2462,2486,2518,2621,2653,2677,2684,2731,2734,2746,2794,2876,3011,3127,3131,3133,3134,3165,3181,3187,3189,3190,3193,3194,3196,3229,3245,3260,3277,3292,3308,3358,3373,3388,3418,3433,3448,3478,3493,3508,3613,3630,3644,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 1793,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 432,1,1⟩,⟨.covers 688,1,1⟩,⟨.covers 2256,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 912,1,1⟩,⟨.covers 2272,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 928,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source50.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source50.rootCodes link50 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual50_011
namespace C13.Global.FastDual50_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,7]
def points : Finset C13.Point := {2,3,6,7}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,979,995,1371,1402,1447,1461,1639,1654,1691,1721,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1955,1957,1969,1987,2411,2425,2455,2486,2647,2677,2731,2746,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2966,2979,2986,2994,3011,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3477,3478,3493,3494,3508,3532,3635,3655,3669,3670,3685,3686,3700,3723,3737,3738,3753,3754,3768,3788,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 135,1,6⟩,⟨.covers 75,1,6⟩,⟨.covers 139,1,6⟩,⟨.covers 77,1,33⟩,⟨.covers 149,1,6⟩,⟨.covers 101,1,6⟩,⟨.covers 89,1,6⟩,⟨.covers 169,1,6⟩,⟨.covers 2369,1,6⟩,⟨.covers 2625,1,6⟩,⟨.covers 78,1,33⟩,⟨.covers 86,1,6⟩,⟨.covers 166,1,6⟩,⟨.covers 154,1,6⟩,⟨.covers 106,1,6⟩,⟨.covers 210,1,33⟩,⟨.covers 226,1,33⟩,⟨.covers 2434,1,6⟩,⟨.covers 2690,1,6⟩,⟨.covers 92,1,33⟩,⟨.covers 108,1,33⟩,⟨.covers 1604,1,6⟩,⟨.covers 1412,1,6⟩,⟨.covers 1352,1,6⟩,⟨.covers 1672,1,6⟩,⟨.covers 2160,1,6⟩,⟨.covers 2224,1,6⟩,⟨.covers 1616,1,6⟩,⟨.covers 1424,1,6⟩,⟨.covers 1376,1,6⟩,⟨.covers 1696,1,6⟩,⟨.covers 1472,1,22⟩,⟨.incident 6,8,-17⟩,⟨.incident 7,8,-17⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source50.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source50.rootCodes link50 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual50_012
namespace C13.Global.FastDual50_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,8]
def points : Finset C13.Point := {2,3,6,8}
def columns : List Code := [254,379,439,506,631,699,758,829,830,949,950,956,979,995,1010,1371,1402,1447,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1852,1882,1957,1972,1987,2002,2300,2411,2425,2455,2485,2486,2537,2552,2647,2677,2731,2739,2745,2746,2773,2804,2876,2921,2966,2996,3011,3041,3056,3251,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3635,3655,3669,3670,3685,3686,3700,3723,3731,3737,3738,3747,3753,3754,3761,3762,3768,3781,3782,3788,3796,3812]
def rows : List LinearRow := [⟨.covers 139,1,6⟩,⟨.covers 77,1,25⟩,⟨.covers 269,1,25⟩,⟨.covers 89,1,25⟩,⟨.covers 169,1,6⟩,⟨.covers 2569,1,6⟩,⟨.covers 270,1,6⟩,⟨.covers 1038,1,25⟩,⟨.covers 778,1,19⟩,⟨.covers 2314,1,25⟩,⟨.covers 1546,1,6⟩,⟨.covers 108,1,25⟩,⟨.covers 1292,1,6⟩,⟨.covers 2316,1,6⟩,⟨.covers 1548,1,19⟩,⟨.covers 664,1,6⟩,⟨.covers 1176,1,6⟩,⟨.covers 680,1,6⟩,⟨.covers 2824,1,19⟩,⟨.covers 3592,1,6⟩,⟨.covers 1376,1,25⟩,⟨.incident 3,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source50.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source50.rootCodes link50 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual50_013
namespace C13.Global.FastDual50_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,8]
def points : Finset C13.Point := {2,3,7,8}
def columns : List Code := [379,439,631,699,829,830,889,890,892,979,995,1371,1401,1402,1447,1461,1509,1639,1651,1653,1654,1691,1721,1753,1852,1882,1912,1957,1987,2017,2411,2425,2426,2455,2486,2518,2647,2675,2677,2678,2731,2746,2794,2876,2921,2936,2966,3011,3026,3187,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3635,3655,3667,3669,3670,3683,3685,3686,3697,3698,3700,3723,3737,3738,3753,3754,3768,3785,3786,3788,3800,3816]
def rows : List LinearRow := [⟨.covers 139,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 77,1,9⟩,⟨.covers 269,1,16⟩,⟨.covers 101,1,4⟩,⟨.covers 197,1,6⟩,⟨.covers 2309,1,13⟩,⟨.covers 1541,1,4⟩,⟨.covers 89,1,6⟩,⟨.covers 1049,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 2089,1,2⟩,⟨.covers 2569,1,1⟩,⟨.covers 2577,1,4⟩,⟨.covers 2817,1,5⟩,⟨.covers 78,1,15⟩,⟨.covers 270,1,16⟩,⟨.covers 86,1,4⟩,⟨.covers 166,1,13⟩,⟨.covers 2566,1,4⟩,⟨.covers 154,1,2⟩,⟨.covers 1050,1,1⟩,⟨.covers 106,1,2⟩,⟨.covers 2090,1,1⟩,⟨.covers 2314,1,2⟩,⟨.covers 1546,1,3⟩,⟨.covers 210,1,5⟩,⟨.covers 226,1,4⟩,⟨.covers 1122,1,4⟩,⟨.covers 1794,1,5⟩,⟨.covers 156,1,11⟩,⟨.covers 108,1,12⟩,⟨.covers 172,1,3⟩,⟨.covers 1292,1,16⟩,⟨.covers 2316,1,7⟩,⟨.covers 116,1,4⟩,⟨.covers 212,1,4⟩,⟨.covers 2820,1,9⟩,⟨.covers 3588,1,4⟩,⟨.covers 184,1,4⟩,⟨.covers 3336,1,5⟩,⟨.covers 3592,1,1⟩,⟨.covers 1424,1,13⟩,⟨.covers 480,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 1696,1,2⟩,⟨.covers 1472,1,1⟩,⟨.incident 2,8,-8⟩,⟨.incident 3,8,-3⟩,⟨.incident 8,8,-1⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source50.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source50.rootCodes link50 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual50_014
namespace C13.Global.FastDual50_015
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,8,9]
def points : Finset C13.Point := {2,3,8,9}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,829,830,892,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1401,1402,1447,1461,1462,1491,1498,1507,1509,1521,1522,1524,1528,1639,1653,1654,1691,1721,1722,1747,1753,1763,1766,1777,1778,1780,1784,1852,1987,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2425,2426,2455,2485,2486,2515,2518,2531,2537,2545,2546,2548,2552,2647,2677,2678,2731,2745,2746,2771,2773,2787,2794,2801,2802,2804,2808,2876,3011,3056,3187,3251,3271,3275,3277,3278,3283,3285,3286,3289,3290,3292,3299,3301,3302,3305,3306,3308,3313,3314,3316,3320,3403,3418,3433,3448,3463,3478,3493,3508,3523,3538,3553,3568,3655,3669,3686,3700,3723,3737,3754,3768,3779,3793,3810,3824]
def rows : List LinearRow := [⟨.covers 263,1,4⟩,⟨.covers 519,1,4⟩,⟨.covers 267,1,4⟩,⟨.covers 523,1,4⟩,⟨.covers 269,1,33⟩,⟨.covers 1037,1,17⟩,⟨.covers 2309,1,2⟩,⟨.covers 1541,1,2⟩,⟨.covers 89,1,4⟩,⟨.covers 169,1,4⟩,⟨.covers 1289,1,6⟩,⟨.covers 2569,1,6⟩,⟨.covers 593,1,2⟩,⟨.covers 657,1,2⟩,⟨.covers 353,1,2⟩,⟨.covers 417,1,2⟩,⟨.covers 1793,1,17⟩,⟨.covers 2817,1,17⟩,⟨.covers 270,1,33⟩,⟨.covers 1038,1,17⟩,⟨.covers 1286,1,2⟩,⟨.covers 2566,1,2⟩,⟨.covers 154,1,4⟩,⟨.covers 106,1,4⟩,⟨.covers 2314,1,6⟩,⟨.covers 1546,1,6⟩,⟨.covers 338,1,2⟩,⟨.covers 402,1,2⟩,⟨.covers 610,1,2⟩,⟨.covers 674,1,2⟩,⟨.covers 92,1,8⟩,⟨.covers 1292,1,33⟩,⟨.covers 2316,1,33⟩,⟨.covers 344,1,4⟩,⟨.covers 1112,1,4⟩,⟨.covers 664,1,4⟩,⟨.covers 1176,1,4⟩,⟨.covers 360,1,4⟩,⟨.covers 2152,1,4⟩,⟨.covers 680,1,4⟩,⟨.covers 2216,1,4⟩,⟨.covers 3336,1,8⟩,⟨.covers 3592,1,8⟩,⟨.covers 848,1,8⟩,⟨.covers 1616,1,4⟩,⟨.covers 1424,1,4⟩,⟨.covers 2656,1,4⟩,⟨.covers 2464,1,4⟩,⟨.incident 3,8,-17⟩,⟨.incident 8,8,-8⟩,⟨.incident 9,8,-8⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source50.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source50.rootCodes link50 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual50_015
