import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source54
namespace C13.Global.FastDual54_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,7]
def points : Finset C13.Point := {2,3,6,7}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,979,995,1371,1402,1447,1461,1639,1654,1691,1721,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1955,1957,1969,1987,2411,2425,2455,2486,2647,2677,2731,2746,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2966,2979,2986,2994,3011,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3477,3478,3493,3494,3508,3532,3635,3655,3669,3670,3685,3686,3700,3723,3737,3738,3753,3754,3768,3788,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 71,1,4⟩,⟨.covers 135,1,1⟩,⟨.covers 1031,1,7⟩,⟨.covers 2055,1,2⟩,⟨.covers 75,1,2⟩,⟨.covers 139,1,5⟩,⟨.covers 1035,1,9⟩,⟨.covers 45,1,19⟩,⟨.covers 77,1,19⟩,⟨.covers 149,1,12⟩,⟨.covers 101,1,3⟩,⟨.covers 2309,1,1⟩,⟨.covers 89,1,4⟩,⟨.covers 169,1,7⟩,⟨.covers 1289,1,3⟩,⟨.covers 3089,1,2⟩,⟨.covers 3105,1,9⟩,⟨.covers 2369,1,1⟩,⟨.covers 2625,1,3⟩,⟨.covers 1793,1,4⟩,⟨.covers 2817,1,1⟩,⟨.covers 46,1,19⟩,⟨.covers 78,1,19⟩,⟨.covers 86,1,7⟩,⟨.covers 166,1,5⟩,⟨.covers 1286,1,3⟩,⟨.covers 2566,1,2⟩,⟨.covers 154,1,3⟩,⟨.covers 106,1,11⟩,⟨.covers 2314,1,3⟩,⟨.covers 210,1,19⟩,⟨.covers 3090,1,9⟩,⟨.covers 226,1,19⟩,⟨.covers 1346,1,1⟩,⟨.covers 1602,1,1⟩,⟨.covers 2434,1,1⟩,⟨.covers 2690,1,5⟩,⟨.covers 92,1,19⟩,⟨.covers 108,1,19⟩,⟨.covers 2316,1,4⟩,⟨.covers 2572,1,6⟩,⟨.covers 116,1,5⟩,⟨.covers 180,1,1⟩,⟨.covers 2580,1,1⟩,⟨.covers 1316,1,1⟩,⟨.covers 1572,1,4⟩,⟨.covers 1412,1,2⟩,⟨.covers 2436,1,2⟩,⟨.covers 120,1,2⟩,⟨.covers 184,1,4⟩,⟨.covers 1304,1,1⟩,⟨.covers 1560,1,3⟩,⟨.covers 2344,1,2⟩,⟨.covers 2600,1,2⟩,⟨.covers 1136,1,2⟩,⟨.covers 2160,1,6⟩,⟨.covers 1200,1,3⟩,⟨.covers 2224,1,5⟩,⟨.covers 2384,1,4⟩,⟨.covers 1808,1,1⟩,⟨.covers 2832,1,4⟩,⟨.covers 1376,1,2⟩,⟨.covers 2464,1,4⟩,⟨.covers 1696,1,2⟩,⟨.covers 1472,1,3⟩,⟨.covers 2496,1,8⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source54.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source54.rootCodes link54 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual54_000
namespace C13.Global.FastDual54_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,9]
def points : Finset C13.Point := {2,3,6,9}
def columns : List Code := [379,439,631,699,829,830,953,954,956,979,995,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1721,1722,1766,1852,1894,1945,1976,1987,2018,2411,2425,2455,2483,2485,2486,2537,2647,2677,2731,2745,2746,2773,2876,2901,2986,3000,3011,3025,3251,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3475,3477,3478,3491,3493,3494,3505,3506,3508,3529,3530,3532,3544,3560,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 1043,1,2⟩,⟨.covers 45,1,10⟩,⟨.covers 77,1,7⟩,⟨.covers 149,1,4⟩,⟨.covers 101,1,10⟩,⟨.covers 1061,1,1⟩,⟨.covers 197,1,8⟩,⟨.covers 773,1,5⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,1⟩,⟨.covers 89,1,4⟩,⟨.covers 169,1,5⟩,⟨.covers 1289,1,2⟩,⟨.covers 2569,1,2⟩,⟨.covers 1553,1,1⟩,⟨.covers 2145,1,2⟩,⟨.covers 1313,1,3⟩,⟨.covers 1793,1,5⟩,⟨.covers 2817,1,3⟩,⟨.covers 46,1,7⟩,⟨.covers 78,1,12⟩,⟨.covers 2070,1,1⟩,⟨.covers 166,1,4⟩,⟨.covers 198,1,3⟩,⟨.covers 774,1,8⟩,⟨.covers 1286,1,4⟩,⟨.covers 2566,1,11⟩,⟨.covers 154,1,2⟩,⟨.covers 1050,1,1⟩,⟨.covers 2090,1,2⟩,⟨.covers 2314,1,5⟩,⟨.covers 1546,1,3⟩,⟨.covers 114,1,1⟩,⟨.covers 210,1,5⟩,⟨.covers 2194,1,3⟩,⟨.covers 226,1,5⟩,⟨.covers 92,1,6⟩,⟨.covers 156,1,10⟩,⟨.covers 108,1,15⟩,⟨.covers 1548,1,15⟩,⟨.covers 2572,1,15⟩,⟨.covers 180,1,4⟩,⟨.covers 3332,1,4⟩,⟨.covers 120,1,3⟩,⟨.covers 184,1,2⟩,⟨.covers 3336,1,2⟩,⟨.covers 3592,1,4⟩,⟨.covers 1136,1,2⟩,⟨.covers 1200,1,1⟩,⟨.covers 1616,1,8⟩,⟨.covers 3344,1,1⟩,⟨.covers 3600,1,2⟩,⟨.covers 2464,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2944,1,1⟩,⟨.incident 2,8,-7⟩,⟨.incident 3,8,-3⟩]
def bound : Int := 6

theorem column_mask : listMask columns = restrictMask universeMask Source54.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source54.rootCodes link54 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual54_001
namespace C13.Global.FastDual54_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,10]
def points : Finset C13.Point := {2,3,6,10}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1498,1639,1654,1691,1715,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2411,2425,2455,2483,2485,2486,2537,2647,2677,2731,2739,2745,2746,2773,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2965,2966,2979,2985,2986,2993,2994,2996,3000,3011,3025,3041,3251,3277,3278,3292,3308,3379,3418,3493,3505,3532,3544,3635,3686,3737,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 2055,1,5⟩,⟨.covers 1035,1,3⟩,⟨.covers 2059,1,5⟩,⟨.covers 45,1,11⟩,⟨.covers 77,1,3⟩,⟨.covers 149,1,4⟩,⟨.covers 101,1,8⟩,⟨.covers 3077,1,7⟩,⟨.covers 89,1,8⟩,⟨.covers 169,1,4⟩,⟨.covers 3329,1,3⟩,⟨.covers 3585,1,11⟩,⟨.covers 46,1,11⟩,⟨.covers 78,1,11⟩,⟨.covers 1286,1,11⟩,⟨.covers 2566,1,3⟩,⟨.covers 106,1,3⟩,⟨.covers 2314,1,3⟩,⟨.covers 1546,1,8⟩,⟨.covers 178,1,1⟩,⟨.covers 210,1,11⟩,⟨.covers 2194,1,2⟩,⟨.covers 226,1,11⟩,⟨.covers 2210,1,2⟩,⟨.covers 92,1,4⟩,⟨.covers 108,1,11⟩,⟨.covers 1292,1,9⟩,⟨.covers 2316,1,2⟩,⟨.covers 2572,1,3⟩,⟨.covers 180,1,5⟩,⟨.covers 212,1,7⟩,⟨.covers 2820,1,3⟩,⟨.covers 3588,1,7⟩,⟨.covers 184,1,5⟩,⟨.covers 2824,1,3⟩,⟨.covers 1136,1,8⟩,⟨.covers 2160,1,3⟩,⟨.covers 1616,1,3⟩,⟨.covers 3344,1,7⟩,⟨.covers 2880,1,8⟩,⟨.covers 1920,1,11⟩,⟨.covers 2944,1,3⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source54.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source54.rootCodes link54 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual54_002
namespace C13.Global.FastDual54_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,11]
def points : Finset C13.Point := {2,3,6,11}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1946,1955,1957,1958,1969,1970,1972,1976,1987,2002,2018,2411,2425,2455,2483,2486,2537,2647,2677,2731,2739,2746,2773,2839,2859,2867,2901,2921,2929,2966,2986,2994,3251,3277,3278,3292,3308,3379,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 3344,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 2464,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source54.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source54.rootCodes link54 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual54_003
namespace C13.Global.FastDual54_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,10,11]
def points : Finset C13.Point := {2,3,10,11}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,823,827,829,830,883,885,886,889,890,892,947,949,950,953,954,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1395,1402,1447,1459,1461,1497,1498,1509,1510,1521,1522,1524,1528,1639,1651,1654,1691,1715,1721,1753,1754,1765,1766,1777,1778,1780,1784,1819,1831,1843,1882,1894,1906,1945,1957,1969,2008,2020,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2419,2425,2455,2483,2486,2517,2518,2537,2538,2545,2546,2548,2552,2647,2675,2677,2731,2739,2746,2773,2774,2793,2794,2801,2802,2804,2808,2839,2859,2867,2901,2921,2929,2966,2986,2994,3028,3048,3056,3187,3251,3277,3278,3292,3308,3313,3314,3316,3320,3379,3532,3568,3635,3788,3824]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 135,1,2⟩,⟨.covers 1031,1,6⟩,⟨.covers 75,1,4⟩,⟨.covers 139,1,8⟩,⟨.covers 1035,1,1⟩,⟨.covers 2059,1,3⟩,⟨.covers 525,1,19⟩,⟨.covers 1037,1,19⟩,⟨.covers 149,1,5⟩,⟨.covers 2309,1,7⟩,⟨.covers 1541,1,6⟩,⟨.covers 169,1,2⟩,⟨.covers 1289,1,11⟩,⟨.covers 2569,1,4⟩,⟨.covers 2145,1,2⟩,⟨.covers 1185,1,4⟩,⟨.covers 705,1,9⟩,⟨.covers 3329,1,19⟩,⟨.covers 3585,1,19⟩,⟨.covers 526,1,19⟩,⟨.covers 1038,1,19⟩,⟨.covers 86,1,2⟩,⟨.covers 1286,1,3⟩,⟨.covers 2566,1,11⟩,⟨.covers 154,1,2⟩,⟨.covers 2314,1,9⟩,⟨.covers 1546,1,5⟩,⟨.covers 114,1,4⟩,⟨.covers 1106,1,1⟩,⟨.covers 1122,1,1⟩,⟨.covers 450,1,9⟩,⟨.covers 706,1,2⟩,⟨.covers 108,1,12⟩,⟨.covers 1292,1,19⟩,⟨.covers 1548,1,19⟩,⟨.covers 404,1,1⟩,⟨.covers 2196,1,3⟩,⟨.covers 420,1,4⟩,⟨.covers 1796,1,4⟩,⟨.covers 2820,1,1⟩,⟨.covers 344,1,2⟩,⟨.covers 1176,1,4⟩,⟨.covers 360,1,1⟩,⟨.covers 680,1,3⟩,⟨.covers 1800,1,2⟩,⟨.covers 2824,1,3⟩,⟨.covers 688,1,5⟩,⟨.covers 2384,1,2⟩,⟨.covers 1616,1,2⟩,⟨.covers 3152,1,5⟩,⟨.covers 1424,1,2⟩,⟨.covers 1376,1,2⟩,⟨.covers 3232,1,8⟩,⟨.covers 1856,1,8⟩,⟨.covers 2880,1,9⟩,⟨.covers 2944,1,4⟩]
def bound : Int := 20

theorem column_mask : listMask columns = restrictMask universeMask Source54.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source54.rootCodes link54 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual54_004
namespace C13.Global.FastDual54_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,9,10]
def points : Finset C13.Point := {2,6,9,10}
def columns : List Code := [379,439,443,445,446,475,491,631,699,829,830,923,939,953,954,956,971,979,995,1211,1262,1339,1371,1402,1435,1447,1453,1459,1461,1465,1498,1639,1646,1654,1691,1721,1766,1894,1945,2235,2269,2363,2395,2411,2425,2455,2459,2461,2462,2475,2483,2485,2486,2489,2490,2492,2507,2521,2537,2647,2653,2677,2715,2731,2745,2746,2773,2845,2876,2901,2955,2969,2986,3000,3011,3025,3131,3227,3251,3257,3277,3278,3292,3308,3355,3379,3418,3469,3481,3493,3505,3532,3544,3686,3737]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 1793,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 2062,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3332,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 3152,1,1⟩,⟨.covers 736,1,1⟩,⟨.covers 2752,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source54.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source54.rootCodes link54 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual54_005
namespace C13.Global.FastDual54_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,9,11]
def points : Finset C13.Point := {2,6,9,11}
def columns : List Code := [379,439,443,445,446,475,491,631,699,829,830,923,939,953,954,956,971,979,995,1211,1262,1339,1371,1387,1402,1435,1447,1451,1453,1454,1459,1461,1462,1465,1466,1468,1483,1498,1514,1639,1646,1654,1691,1707,1721,1722,1766,1838,1852,1894,1931,1945,1962,1976,1987,2018,2235,2269,2363,2411,2425,2455,2462,2475,2483,2486,2490,2537,2647,2653,2677,2731,2746,2773,2901,2986,3131,3243,3251,3258,3277,3278,3292,3308,3371,3379,3433,3470,3478,3498,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 135,1,7⟩,⟨.covers 1031,1,4⟩,⟨.covers 75,1,1⟩,⟨.covers 523,1,7⟩,⟨.covers 2059,1,3⟩,⟨.covers 99,1,5⟩,⟨.covers 1539,1,1⟩,⟨.covers 45,1,4⟩,⟨.covers 525,1,7⟩,⟨.covers 1037,1,7⟩,⟨.covers 2309,1,4⟩,⟨.covers 1049,1,3⟩,⟨.covers 2089,1,1⟩,⟨.covers 201,1,3⟩,⟨.covers 3081,1,1⟩,⟨.covers 1073,1,3⟩,⟨.covers 1793,1,3⟩,⟨.covers 2817,1,1⟩,⟨.covers 3329,1,5⟩,⟨.covers 3585,1,11⟩,⟨.covers 2062,1,4⟩,⟨.covers 54,1,4⟩,⟨.covers 198,1,3⟩,⟨.covers 774,1,7⟩,⟨.covers 2566,1,11⟩,⟨.covers 3078,1,3⟩,⟨.covers 210,1,7⟩,⟨.covers 156,1,7⟩,⟨.covers 108,1,7⟩,⟨.covers 1548,1,3⟩,⟨.covers 2572,1,4⟩,⟨.covers 1796,1,1⟩,⟨.covers 3332,1,3⟩,⟨.covers 120,1,4⟩,⟨.covers 2824,1,11⟩,⟨.covers 3592,1,11⟩,⟨.covers 1136,1,7⟩,⟨.covers 688,1,4⟩,⟨.covers 1200,1,1⟩,⟨.covers 2224,1,7⟩,⟨.covers 720,1,4⟩,⟨.covers 1232,1,4⟩,⟨.covers 2384,1,6⟩,⟨.covers 1808,1,5⟩,⟨.covers 3344,1,3⟩,⟨.covers 736,1,5⟩,⟨.covers 2656,1,11⟩,⟨.covers 3168,1,3⟩,⟨.covers 2496,1,7⟩,⟨.covers 1728,1,2⟩,⟨.covers 2752,1,7⟩,⟨.covers 1856,1,3⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source54.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source54.rootCodes link54 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual54_006
namespace C13.Global.FastDual54_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,10,11]
def points : Finset C13.Point := {2,6,10,11}
def columns : List Code := [379,439,443,445,446,475,491,631,699,823,827,829,830,859,875,883,923,939,947,949,950,953,954,956,971,979,995,1211,1262,1339,1371,1402,1435,1447,1453,1459,1461,1465,1498,1595,1639,1646,1654,1691,1715,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2235,2269,2363,2411,2425,2455,2462,2475,2483,2486,2490,2537,2619,2647,2653,2677,2731,2739,2746,2773,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3251,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,7⟩,⟨.covers 135,1,9⟩,⟨.covers 75,1,4⟩,⟨.covers 1035,1,5⟩,⟨.covers 2059,1,5⟩,⟨.covers 45,1,9⟩,⟨.covers 525,1,2⟩,⟨.covers 197,1,5⟩,⟨.covers 2309,1,2⟩,⟨.covers 1541,1,4⟩,⟨.covers 3077,1,5⟩,⟨.covers 1289,1,2⟩,⟨.covers 2569,1,2⟩,⟨.covers 3329,1,11⟩,⟨.covers 3585,1,11⟩,⟨.covers 526,1,11⟩,⟨.covers 2062,1,5⟩,⟨.covers 86,1,4⟩,⟨.covers 1286,1,2⟩,⟨.covers 3078,1,5⟩,⟨.covers 650,1,2⟩,⟨.covers 2314,1,2⟩,⟨.covers 210,1,7⟩,⟨.covers 2316,1,4⟩,⟨.covers 2572,1,7⟩,⟨.covers 180,1,2⟩,⟨.covers 1796,1,5⟩,⟨.covers 2820,1,9⟩,⟨.covers 3588,1,4⟩,⟨.covers 120,1,7⟩,⟨.covers 1560,1,4⟩,⟨.covers 680,1,2⟩,⟨.covers 2824,1,2⟩,⟨.covers 2160,1,4⟩,⟨.covers 1200,1,5⟩,⟨.covers 2224,1,5⟩,⟨.covers 720,1,4⟩,⟨.covers 1616,1,7⟩,⟨.covers 3152,1,11⟩,⟨.covers 1424,1,4⟩,⟨.covers 2704,1,2⟩,⟨.covers 736,1,11⟩,⟨.covers 1376,1,4⟩,⟨.covers 2656,1,7⟩,⟨.covers 3168,1,11⟩,⟨.covers 2464,1,4⟩,⟨.covers 2496,1,7⟩,⟨.covers 1920,1,2⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source54.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source54.rootCodes link54 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual54_007
