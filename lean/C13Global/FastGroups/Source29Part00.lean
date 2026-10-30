import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source29
namespace C13.Global.FastDual29_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,7]
def points : Finset C13.Point := {2,3,6,7}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,979,995,1371,1402,1447,1461,1639,1654,1691,1721,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1955,1957,1969,1987,2411,2425,2455,2486,2647,2677,2731,2746,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2966,2979,2986,2994,3011,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3477,3478,3493,3494,3508,3532,3635,3655,3669,3670,3685,3686,3700,3723,3737,3738,3753,3754,3768,3788,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 135,1,11⟩,⟨.covers 139,1,11⟩,⟨.covers 77,1,33⟩,⟨.covers 149,1,13⟩,⟨.covers 169,1,13⟩,⟨.covers 1409,1,6⟩,⟨.covers 1665,1,6⟩,⟨.covers 78,1,33⟩,⟨.covers 166,1,9⟩,⟨.covers 154,1,9⟩,⟨.covers 210,1,33⟩,⟨.covers 226,1,33⟩,⟨.covers 2434,1,6⟩,⟨.covers 2690,1,6⟩,⟨.covers 92,1,33⟩,⟨.covers 108,1,33⟩,⟨.covers 1412,1,7⟩,⟨.covers 2436,1,4⟩,⟨.covers 1672,1,7⟩,⟨.covers 2696,1,4⟩,⟨.covers 1200,1,4⟩,⟨.covers 2224,1,7⟩,⟨.covers 1424,1,4⟩,⟨.covers 2704,1,7⟩,⟨.covers 2464,1,7⟩,⟨.covers 1696,1,4⟩,⟨.covers 1472,1,22⟩,⟨.incident 7,8,-33⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source29.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source29.rootCodes link29 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual29_000
namespace C13.Global.FastDual29_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,9]
def points : Finset C13.Point := {2,3,6,9}
def columns : List Code := [379,439,631,699,829,830,953,954,956,979,995,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1721,1722,1766,1852,1894,1945,1976,1987,2018,2411,2425,2455,2483,2485,2486,2537,2647,2677,2731,2745,2746,2773,2876,2901,2986,3000,3011,3025,3251,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3475,3477,3478,3491,3493,3494,3505,3506,3508,3529,3530,3532,3544,3560,3655,3669,3686,3700,3723,3737,3754,3768,3853,3884,3909,3940,3977,4008,4033,4064]
def rows : List LinearRow := [⟨.covers 75,1,7⟩,⟨.covers 77,1,21⟩,⟨.covers 101,1,28⟩,⟨.covers 89,1,7⟩,⟨.covers 201,1,7⟩,⟨.covers 78,1,28⟩,⟨.covers 2566,1,28⟩,⟨.covers 106,1,7⟩,⟨.covers 210,1,24⟩,⟨.covers 226,1,28⟩,⟨.covers 92,1,3⟩,⟨.covers 108,1,21⟩,⟨.covers 212,1,24⟩,⟨.covers 120,1,7⟩,⟨.covers 232,1,7⟩,⟨.covers 1352,1,3⟩,⟨.covers 2376,1,14⟩,⟨.covers 720,1,3⟩,⟨.covers 1616,1,28⟩,⟨.covers 2880,1,24⟩,⟨.covers 3392,1,3⟩,⟨.incident 6,8,-28⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source29.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source29.rootCodes link29 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual29_001
namespace C13.Global.FastDual29_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,10]
def points : Finset C13.Point := {2,3,6,10}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1498,1639,1654,1691,1715,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2411,2425,2455,2483,2485,2486,2537,2647,2677,2731,2739,2745,2746,2773,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2965,2966,2979,2985,2986,2993,2994,2996,3000,3011,3025,3041,3251,3277,3278,3292,3308,3379,3418,3493,3505,3532,3544,3635,3686,3737,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 1031,1,11⟩,⟨.covers 2055,1,5⟩,⟨.covers 75,1,3⟩,⟨.covers 2059,1,3⟩,⟨.covers 77,1,4⟩,⟨.covers 269,1,11⟩,⟨.covers 149,1,4⟩,⟨.covers 197,1,7⟩,⟨.covers 89,1,8⟩,⟨.covers 169,1,4⟩,⟨.covers 2569,1,1⟩,⟨.covers 3329,1,11⟩,⟨.covers 3585,1,9⟩,⟨.covers 78,1,9⟩,⟨.covers 270,1,11⟩,⟨.covers 86,1,3⟩,⟨.covers 2566,1,3⟩,⟨.covers 3078,1,2⟩,⟨.covers 2314,1,5⟩,⟨.covers 1546,1,11⟩,⟨.covers 178,1,1⟩,⟨.covers 210,1,11⟩,⟨.covers 2194,1,2⟩,⟨.covers 226,1,11⟩,⟨.covers 2210,1,2⟩,⟨.covers 92,1,5⟩,⟨.covers 108,1,11⟩,⟨.covers 1292,1,11⟩,⟨.covers 2572,1,7⟩,⟨.covers 116,1,8⟩,⟨.covers 180,1,5⟩,⟨.covers 2820,1,3⟩,⟨.covers 3588,1,4⟩,⟨.covers 184,1,5⟩,⟨.covers 2824,1,1⟩,⟨.covers 2160,1,3⟩,⟨.covers 3152,1,6⟩,⟨.covers 1376,1,11⟩,⟨.covers 3616,1,1⟩,⟨.covers 2880,1,8⟩,⟨.covers 1920,1,11⟩,⟨.covers 2944,1,3⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source29.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source29.rootCodes link29 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual29_002
namespace C13.Global.FastDual29_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,11]
def points : Finset C13.Point := {2,3,6,11}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1946,1955,1957,1958,1969,1970,1972,1976,1987,2002,2018,2411,2425,2455,2483,2486,2537,2647,2677,2731,2739,2746,2773,2839,2859,2867,2901,2921,2929,2966,2986,2994,3251,3277,3278,3292,3308,3379,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 71,1,8⟩,⟨.covers 135,1,5⟩,⟨.covers 2055,1,3⟩,⟨.covers 139,1,5⟩,⟨.covers 2059,1,3⟩,⟨.covers 77,1,11⟩,⟨.covers 269,1,11⟩,⟨.covers 149,1,3⟩,⟨.covers 101,1,3⟩,⟨.covers 89,1,11⟩,⟨.covers 169,1,3⟩,⟨.covers 1409,1,2⟩,⟨.covers 1665,1,2⟩,⟨.covers 1793,1,1⟩,⟨.covers 3329,1,11⟩,⟨.covers 3585,1,11⟩,⟨.covers 78,1,4⟩,⟨.covers 270,1,11⟩,⟨.covers 1286,1,4⟩,⟨.covers 3078,1,7⟩,⟨.covers 2314,1,8⟩,⟨.covers 1546,1,4⟩,⟨.covers 210,1,11⟩,⟨.covers 226,1,11⟩,⟨.covers 92,1,11⟩,⟨.covers 108,1,5⟩,⟨.covers 172,1,5⟩,⟨.covers 2316,1,11⟩,⟨.covers 2572,1,3⟩,⟨.covers 180,1,3⟩,⟨.covers 1796,1,5⟩,⟨.covers 2820,1,8⟩,⟨.covers 184,1,3⟩,⟨.covers 1800,1,5⟩,⟨.covers 1136,1,11⟩,⟨.covers 1200,1,3⟩,⟨.covers 2224,1,8⟩,⟨.covers 2656,1,8⟩,⟨.covers 2752,1,7⟩,⟨.covers 2880,1,3⟩,⟨.covers 2944,1,3⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source29.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source29.rootCodes link29 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual29_003
namespace C13.Global.FastDual29_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,10,11]
def points : Finset C13.Point := {2,3,10,11}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,823,827,829,830,883,885,886,889,890,892,947,949,950,953,954,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1395,1402,1447,1459,1461,1497,1498,1509,1510,1521,1522,1524,1528,1639,1651,1654,1691,1715,1721,1753,1754,1765,1766,1777,1778,1780,1784,1819,1831,1843,1882,1894,1906,1945,1957,1969,2008,2020,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2419,2425,2455,2483,2486,2517,2518,2537,2538,2545,2546,2548,2552,2647,2675,2677,2731,2739,2746,2773,2774,2793,2794,2801,2802,2804,2808,2839,2859,2867,2901,2921,2929,2966,2986,2994,3028,3048,3056,3187,3251,3277,3278,3292,3308,3313,3314,3316,3320,3379,3532,3568,3635,3788,3824]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 135,1,5⟩,⟨.covers 1031,1,6⟩,⟨.covers 75,1,4⟩,⟨.covers 139,1,9⟩,⟨.covers 2059,1,3⟩,⟨.covers 269,1,19⟩,⟨.covers 1037,1,19⟩,⟨.covers 149,1,5⟩,⟨.covers 2309,1,9⟩,⟨.covers 1541,1,8⟩,⟨.covers 89,1,2⟩,⟨.covers 1289,1,12⟩,⟨.covers 2569,1,7⟩,⟨.covers 2145,1,3⟩,⟨.covers 1185,1,3⟩,⟨.covers 705,1,9⟩,⟨.covers 3329,1,19⟩,⟨.covers 3585,1,19⟩,⟨.covers 270,1,19⟩,⟨.covers 1038,1,19⟩,⟨.covers 86,1,2⟩,⟨.covers 1286,1,2⟩,⟨.covers 2566,1,9⟩,⟨.covers 154,1,1⟩,⟨.covers 2314,1,6⟩,⟨.covers 1546,1,5⟩,⟨.covers 178,1,4⟩,⟨.covers 1122,1,3⟩,⟨.covers 450,1,9⟩,⟨.covers 706,1,2⟩,⟨.covers 92,1,5⟩,⟨.covers 108,1,7⟩,⟨.covers 1292,1,19⟩,⟨.covers 1548,1,19⟩,⟨.covers 596,1,1⟩,⟨.covers 2132,1,4⟩,⟨.covers 420,1,4⟩,⟨.covers 1796,1,4⟩,⟨.covers 2820,1,1⟩,⟨.covers 1112,1,1⟩,⟨.covers 664,1,1⟩,⟨.covers 1176,1,2⟩,⟨.covers 360,1,3⟩,⟨.covers 1800,1,2⟩,⟨.covers 2824,1,3⟩,⟨.covers 688,1,4⟩,⟨.covers 2384,1,1⟩,⟨.covers 1616,1,2⟩,⟨.covers 1424,1,2⟩,⟨.covers 1376,1,2⟩,⟨.covers 3168,1,12⟩,⟨.covers 2464,1,2⟩,⟨.covers 1856,1,9⟩,⟨.covers 2880,1,3⟩,⟨.covers 2944,1,9⟩]
def bound : Int := 20

theorem column_mask : listMask columns = restrictMask universeMask Source29.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source29.rootCodes link29 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual29_004
namespace C13.Global.FastDual29_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,9]
def points : Finset C13.Point := {2,6,7,9}
def columns : List Code := [379,439,631,699,829,830,923,939,971,979,995,1339,1371,1387,1402,1447,1453,1461,1639,1646,1654,1691,1707,1721,1838,1852,1894,1931,1945,1987,2363,2395,2411,2425,2455,2462,2486,2647,2653,2677,2715,2731,2746,2845,2876,2901,2955,2986,3011,3131,3277,3278,3292,3308,3355,3371,3379,3385,3386,3403,3417,3418,3433,3434,3448,3463,3469,3470,3477,3478,3484,3493,3494,3500,3508,3532,3655,3669,3686,3700,3723,3737,3754,3768,3853,3884,3909,3940,3977,4008,4033,4064]
def rows : List LinearRow := [⟨.covers 75,1,1⟩,⟨.covers 101,1,2⟩,⟨.covers 197,1,2⟩,⟨.covers 78,1,2⟩,⟨.covers 2566,1,2⟩,⟨.covers 210,1,2⟩,⟨.covers 226,1,2⟩,⟨.covers 1346,1,1⟩,⟨.covers 92,1,2⟩,⟨.covers 228,1,2⟩,⟨.covers 120,1,1⟩,⟨.covers 2384,1,1⟩,⟨.covers 1616,1,2⟩,⟨.covers 1728,1,1⟩,⟨.covers 2752,1,1⟩,⟨.incident 6,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source29.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source29.rootCodes link29 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual29_005
namespace C13.Global.FastDual29_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,10]
def points : Finset C13.Point := {2,6,7,10}
def columns : List Code := [379,439,631,699,823,827,829,830,859,875,883,923,939,947,971,979,995,1339,1371,1402,1447,1453,1461,1595,1639,1646,1654,1691,1721,1819,1831,1843,1882,1894,1906,1945,1957,1969,2363,2395,2411,2425,2455,2462,2486,2619,2647,2653,2677,2715,2731,2746,2839,2843,2845,2846,2859,2867,2869,2870,2873,2874,2876,2891,2899,2901,2905,2915,2921,2929,2955,2963,2966,2970,2979,2986,2994,3011,3131,3277,3278,3292,3308,3355,3379,3418,3469,3493,3532,3611,3635,3662,3686,3737,3788]
def rows : List LinearRow := [⟨.covers 2055,1,11⟩,⟨.covers 75,1,3⟩,⟨.covers 139,1,3⟩,⟨.covers 1035,1,8⟩,⟨.covers 2059,1,3⟩,⟨.covers 77,1,7⟩,⟨.covers 269,1,7⟩,⟨.covers 525,1,3⟩,⟨.covers 101,1,11⟩,⟨.covers 197,1,3⟩,⟨.covers 169,1,3⟩,⟨.covers 270,1,3⟩,⟨.covers 526,1,7⟩,⟨.covers 198,1,11⟩,⟨.covers 1286,1,11⟩,⟨.covers 106,1,3⟩,⟨.covers 210,1,11⟩,⟨.covers 226,1,11⟩,⟨.covers 156,1,7⟩,⟨.covers 180,1,11⟩,⟨.covers 212,1,3⟩,⟨.covers 228,1,11⟩,⟨.covers 120,1,5⟩,⟨.covers 184,1,5⟩,⟨.covers 2344,1,2⟩,⟨.covers 2600,1,2⟩,⟨.covers 1800,1,3⟩,⟨.covers 1136,1,3⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,8⟩,⟨.covers 2704,1,4⟩,⟨.covers 1696,1,3⟩,⟨.covers 2848,1,1⟩,⟨.covers 3360,1,11⟩,⟨.covers 3616,1,11⟩,⟨.covers 1472,1,4⟩,⟨.covers 1728,1,4⟩,⟨.covers 2880,1,5⟩,⟨.covers 3392,1,7⟩,⟨.covers 1920,1,8⟩,⟨.covers 2944,1,5⟩,⟨.covers 3712,1,7⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source29.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source29.rootCodes link29 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual29_006
namespace C13.Global.FastDual29_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,11]
def points : Finset C13.Point := {2,6,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,859,875,883,923,939,947,971,979,995,1339,1371,1387,1402,1447,1453,1461,1595,1639,1646,1654,1691,1707,1721,1819,1831,1835,1837,1838,1843,1845,1846,1849,1850,1852,1867,1875,1882,1891,1894,1898,1906,1931,1939,1945,1955,1957,1961,1969,1987,2363,2411,2425,2455,2462,2486,2619,2647,2653,2677,2731,2746,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3277,3278,3292,3308,3371,3379,3433,3470,3478,3532,3627,3635,3661,3669,3754,3788]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 1031,1,8⟩,⟨.covers 75,1,6⟩,⟨.covers 139,1,6⟩,⟨.covers 2059,1,3⟩,⟨.covers 141,1,6⟩,⟨.covers 269,1,3⟩,⟨.covers 525,1,6⟩,⟨.covers 149,1,8⟩,⟨.covers 197,1,6⟩,⟨.covers 2309,1,3⟩,⟨.covers 1049,1,3⟩,⟨.covers 169,1,3⟩,⟨.covers 3089,1,3⟩,⟨.covers 3329,1,8⟩,⟨.covers 3585,1,6⟩,⟨.covers 78,1,8⟩,⟨.covers 142,1,3⟩,⟨.covers 270,1,8⟩,⟨.covers 86,1,8⟩,⟨.covers 166,1,3⟩,⟨.covers 1050,1,3⟩,⟨.covers 106,1,3⟩,⟨.covers 210,1,11⟩,⟨.covers 226,1,11⟩,⟨.covers 92,1,3⟩,⟨.covers 540,1,3⟩,⟨.covers 228,1,6⟩,⟨.covers 1796,1,3⟩,⟨.covers 2820,1,8⟩,⟨.covers 120,1,3⟩,⟨.covers 184,1,3⟩,⟨.covers 2824,1,8⟩,⟨.covers 2160,1,8⟩,⟨.covers 2224,1,8⟩,⟨.covers 1616,1,3⟩,⟨.covers 1424,1,3⟩,⟨.covers 3216,1,8⟩,⟨.covers 1376,1,3⟩,⟨.covers 2656,1,3⟩,⟨.covers 1696,1,3⟩,⟨.covers 3232,1,6⟩,⟨.covers 3616,1,3⟩,⟨.covers 2496,1,11⟩,⟨.covers 2752,1,11⟩,⟨.covers 1856,1,6⟩,⟨.covers 1920,1,6⟩,⟨.covers 2944,1,3⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source29.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source29.rootCodes link29 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual29_007
