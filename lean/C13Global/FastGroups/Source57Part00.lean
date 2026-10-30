import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source57
namespace C13.Global.FastDual57_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,5,10]
def points : Finset C13.Point := {2,3,5,10}
def columns : List Code := [254,508,829,830,892,956,979,1243,1255,1270,1371,1447,1461,1497,1498,1509,1524,1639,1654,1691,1753,1754,1766,1819,1831,1882,1894,1945,1957,2008,2020,2263,2283,2298,2411,2425,2455,2515,2517,2518,2537,2552,2647,2731,2746,2771,2773,2774,2794,2839,2859,2873,2874,2876,2899,2901,2902,2921,2922,2936,2963,2965,2966,2985,2986,3000,3011,3025,3026,3028,3048,3187,3251,3277,3278,3289,3290,3292,3314,3379,3418,3493,3505,3532,3544,3568,3635,3686,3698,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 45,1,2⟩,⟨.covers 77,1,2⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,2⟩,⟨.covers 2309,1,1⟩,⟨.covers 526,1,2⟩,⟨.covers 1038,1,2⟩,⟨.covers 1286,1,2⟩,⟨.covers 2566,1,1⟩,⟨.covers 2316,1,2⟩,⟨.covers 1548,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 596,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 1696,1,2⟩,⟨.incident 2,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source57.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source57.rootCodes link57 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual57_000
namespace C13.Global.FastDual57_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,7]
def points : Finset C13.Point := {2,3,6,7}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,979,995,1371,1402,1447,1461,1639,1654,1691,1721,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1955,1957,1969,1987,2411,2425,2455,2486,2647,2677,2731,2746,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2966,2979,2986,2994,3011,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3477,3478,3493,3494,3508,3532,3635,3655,3669,3670,3685,3686,3700,3723,3737,3738,3753,3754,3768,3788,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 135,1,5⟩,⟨.covers 1031,1,9⟩,⟨.covers 75,1,4⟩,⟨.covers 139,1,1⟩,⟨.covers 1035,1,7⟩,⟨.covers 2059,1,2⟩,⟨.covers 45,1,19⟩,⟨.covers 77,1,19⟩,⟨.covers 149,1,7⟩,⟨.covers 101,1,4⟩,⟨.covers 1541,1,3⟩,⟨.covers 89,1,3⟩,⟨.covers 169,1,12⟩,⟨.covers 2569,1,1⟩,⟨.covers 3089,1,9⟩,⟨.covers 3105,1,2⟩,⟨.covers 2369,1,3⟩,⟨.covers 2625,1,1⟩,⟨.covers 1793,1,4⟩,⟨.covers 46,1,19⟩,⟨.covers 78,1,19⟩,⟨.covers 86,1,11⟩,⟨.covers 166,1,3⟩,⟨.covers 2566,1,3⟩,⟨.covers 154,1,5⟩,⟨.covers 106,1,7⟩,⟨.covers 2314,1,2⟩,⟨.covers 1546,1,3⟩,⟨.covers 210,1,19⟩,⟨.covers 226,1,19⟩,⟨.covers 3106,1,9⟩,⟨.covers 1346,1,1⟩,⟨.covers 1602,1,1⟩,⟨.covers 2434,1,5⟩,⟨.covers 2690,1,1⟩,⟨.covers 92,1,19⟩,⟨.covers 108,1,19⟩,⟨.covers 2316,1,8⟩,⟨.covers 1548,1,2⟩,⟨.covers 116,1,2⟩,⟨.covers 180,1,4⟩,⟨.covers 2324,1,2⟩,⟨.covers 2580,1,2⟩,⟨.covers 1316,1,3⟩,⟨.covers 1572,1,1⟩,⟨.covers 120,1,5⟩,⟨.covers 184,1,1⟩,⟨.covers 1304,1,4⟩,⟨.covers 1560,1,1⟩,⟨.covers 2344,1,1⟩,⟨.covers 1672,1,2⟩,⟨.covers 2696,1,3⟩,⟨.covers 1136,1,2⟩,⟨.covers 2160,1,6⟩,⟨.covers 1200,1,4⟩,⟨.covers 2224,1,5⟩,⟨.covers 1616,1,2⟩,⟨.covers 1424,1,2⟩,⟨.covers 2704,1,4⟩,⟨.covers 2656,1,4⟩,⟨.covers 1824,1,1⟩,⟨.covers 2848,1,4⟩,⟨.covers 1472,1,2⟩,⟨.covers 2496,1,8⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source57.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source57.rootCodes link57 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual57_001
namespace C13.Global.FastDual57_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,10]
def points : Finset C13.Point := {2,3,6,10}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1498,1639,1654,1691,1715,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2411,2425,2455,2483,2485,2486,2537,2647,2677,2731,2739,2745,2746,2773,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2965,2966,2979,2985,2986,2993,2994,2996,3000,3011,3025,3041,3251,3277,3278,3292,3308,3379,3418,3493,3505,3532,3544,3635,3686,3737,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 2880,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source57.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source57.rootCodes link57 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual57_002
namespace C13.Global.FastDual57_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,11]
def points : Finset C13.Point := {2,3,6,11}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1946,1955,1957,1958,1969,1970,1972,1976,1987,2002,2018,2411,2425,2455,2483,2486,2537,2647,2677,2731,2739,2746,2773,2839,2859,2867,2901,2921,2929,2966,2986,2994,3251,3277,3278,3292,3308,3379,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 71,1,11⟩,⟨.covers 135,1,3⟩,⟨.covers 139,1,3⟩,⟨.covers 2059,1,5⟩,⟨.covers 45,1,11⟩,⟨.covers 77,1,11⟩,⟨.covers 149,1,3⟩,⟨.covers 2309,1,5⟩,⟨.covers 89,1,11⟩,⟨.covers 169,1,3⟩,⟨.covers 1409,1,3⟩,⟨.covers 1665,1,3⟩,⟨.covers 3329,1,8⟩,⟨.covers 3585,1,11⟩,⟨.covers 46,1,11⟩,⟨.covers 78,1,8⟩,⟨.covers 1286,1,5⟩,⟨.covers 2314,1,5⟩,⟨.covers 1546,1,5⟩,⟨.covers 3082,1,3⟩,⟨.covers 210,1,11⟩,⟨.covers 226,1,11⟩,⟨.covers 92,1,3⟩,⟨.covers 108,1,11⟩,⟨.covers 2316,1,3⟩,⟨.covers 2572,1,8⟩,⟨.covers 180,1,5⟩,⟨.covers 212,1,5⟩,⟨.covers 1796,1,5⟩,⟨.covers 2820,1,5⟩,⟨.covers 184,1,5⟩,⟨.covers 1800,1,5⟩,⟨.covers 1136,1,11⟩,⟨.covers 2224,1,5⟩,⟨.covers 3216,1,3⟩,⟨.covers 2656,1,11⟩,⟨.covers 3360,1,3⟩,⟨.covers 2496,1,8⟩,⟨.covers 2944,1,5⟩,⟨.covers 3712,1,3⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source57.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source57.rootCodes link57 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual57_003
namespace C13.Global.FastDual57_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,10,11]
def points : Finset C13.Point := {2,3,10,11}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,823,827,829,830,883,885,886,889,890,892,947,949,950,953,954,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1395,1402,1447,1459,1461,1497,1498,1509,1510,1521,1522,1524,1528,1639,1651,1654,1691,1715,1721,1753,1754,1765,1766,1777,1778,1780,1784,1819,1831,1843,1882,1894,1906,1945,1957,1969,2008,2020,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2419,2425,2455,2483,2486,2517,2518,2537,2538,2545,2546,2548,2552,2647,2675,2677,2731,2739,2746,2773,2774,2793,2794,2801,2802,2804,2808,2839,2859,2867,2901,2921,2929,2966,2986,2994,3028,3048,3056,3187,3251,3277,3278,3292,3308,3313,3314,3316,3320,3379,3532,3568,3635,3788,3824]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 135,1,7⟩,⟨.covers 1031,1,2⟩,⟨.covers 2055,1,4⟩,⟨.covers 75,1,3⟩,⟨.covers 139,1,6⟩,⟨.covers 1035,1,5⟩,⟨.covers 525,1,19⟩,⟨.covers 1037,1,19⟩,⟨.covers 149,1,2⟩,⟨.covers 101,1,1⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,11⟩,⟨.covers 169,1,5⟩,⟨.covers 1289,1,8⟩,⟨.covers 2569,1,7⟩,⟨.covers 2129,1,3⟩,⟨.covers 1169,1,2⟩,⟨.covers 1185,1,2⟩,⟨.covers 449,1,9⟩,⟨.covers 3329,1,19⟩,⟨.covers 3585,1,19⟩,⟨.covers 526,1,19⟩,⟨.covers 1038,1,19⟩,⟨.covers 166,1,4⟩,⟨.covers 1286,1,4⟩,⟨.covers 2566,1,7⟩,⟨.covers 106,1,1⟩,⟨.covers 2314,1,12⟩,⟨.covers 1546,1,2⟩,⟨.covers 114,1,4⟩,⟨.covers 1106,1,3⟩,⟨.covers 2194,1,1⟩,⟨.covers 450,1,2⟩,⟨.covers 706,1,9⟩,⟨.covers 108,1,11⟩,⟨.covers 1292,1,19⟩,⟨.covers 1548,1,19⟩,⟨.covers 596,1,2⟩,⟨.covers 404,1,2⟩,⟨.covers 612,1,1⟩,⟨.covers 1124,1,2⟩,⟨.covers 420,1,1⟩,⟨.covers 1796,1,2⟩,⟨.covers 2820,1,4⟩,⟨.covers 664,1,4⟩,⟨.covers 2152,1,3⟩,⟨.covers 680,1,1⟩,⟨.covers 1800,1,4⟩,⟨.covers 2824,1,1⟩,⟨.covers 368,1,1⟩,⟨.covers 432,1,4⟩,⟨.covers 1616,1,2⟩,⟨.covers 3152,1,10⟩,⟨.covers 1376,1,2⟩,⟨.covers 2656,1,3⟩,⟨.covers 2464,1,1⟩,⟨.covers 1696,1,2⟩,⟨.covers 3232,1,2⟩,⟨.covers 1856,1,8⟩,⟨.covers 2880,1,6⟩,⟨.covers 2944,1,5⟩]
def bound : Int := 20

theorem column_mask : listMask columns = restrictMask universeMask Source57.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source57.rootCodes link57 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual57_004
namespace C13.Global.FastDual57_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,5,6,10]
def points : Finset C13.Point := {2,5,6,10}
def columns : List Code := [445,475,829,830,859,923,956,971,979,1371,1435,1447,1453,1461,1498,1639,1646,1654,1691,1766,1819,1831,1882,1894,1945,1957,2235,2269,2363,2395,2411,2425,2455,2459,2461,2462,2475,2489,2507,2521,2537,2619,2647,2653,2715,2731,2746,2773,2839,2843,2845,2846,2859,2873,2874,2876,2891,2899,2901,2905,2921,2955,2963,2965,2966,2969,2970,2972,2985,2986,3000,3011,3017,3025,3131,3227,3251,3277,3278,3292,3355,3379,3418,3469,3481,3493,3505,3532,3544,3611,3635,3662,3686,3737,3788]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 197,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 3152,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 2880,1,1⟩,⟨.covers 1920,1,1⟩,⟨.covers 3712,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source57.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source57.rootCodes link57 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual57_005
namespace C13.Global.FastDual57_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,5,6,11]
def points : Finset C13.Point := {2,5,6,11}
def columns : List Code := [445,475,829,830,859,923,956,971,979,1371,1435,1447,1453,1461,1483,1498,1639,1646,1654,1691,1766,1819,1831,1837,1838,1845,1846,1852,1867,1875,1882,1894,1931,1939,1945,1946,1957,1958,1964,1972,1987,1994,2002,2235,2269,2363,2411,2425,2455,2462,2475,2537,2619,2647,2653,2731,2746,2773,2839,2859,2901,2921,2966,2986,3131,3243,3251,3277,3278,3292,3371,3379,3433,3470,3478,3532,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 71,1,8⟩,⟨.covers 135,1,2⟩,⟨.covers 75,1,5⟩,⟨.covers 83,1,5⟩,⟨.covers 163,1,3⟩,⟨.covers 2563,1,2⟩,⟨.covers 45,1,3⟩,⟨.covers 141,1,1⟩,⟨.covers 53,1,1⟩,⟨.covers 101,1,10⟩,⟨.covers 197,1,13⟩,⟨.covers 773,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 1185,1,1⟩,⟨.covers 897,1,3⟩,⟨.covers 3585,1,1⟩,⟨.covers 78,1,6⟩,⟨.covers 142,1,3⟩,⟨.covers 54,1,2⟩,⟨.covers 58,1,3⟩,⟨.covers 1050,1,3⟩,⟨.covers 202,1,5⟩,⟨.covers 114,1,16⟩,⟨.covers 226,1,17⟩,⟨.covers 540,1,2⟩,⟨.covers 108,1,11⟩,⟨.covers 172,1,2⟩,⟨.covers 2572,1,13⟩,⟨.covers 3588,1,1⟩,⟨.covers 120,1,17⟩,⟨.covers 1112,1,2⟩,⟨.covers 232,1,17⟩,⟨.covers 680,1,2⟩,⟨.covers 1328,1,5⟩,⟨.covers 2608,1,2⟩,⟨.covers 848,1,5⟩,⟨.covers 3152,1,13⟩,⟨.covers 864,1,10⟩,⟨.covers 3168,1,8⟩,⟨.covers 928,1,2⟩,⟨.covers 3232,1,2⟩,⟨.covers 3616,1,2⟩,⟨.covers 1472,1,5⟩,⟨.covers 2752,1,1⟩,⟨.covers 1856,1,5⟩,⟨.covers 2880,1,8⟩,⟨.covers 3392,1,10⟩,⟨.covers 2944,1,3⟩,⟨.incident 5,8,-3⟩,⟨.incident 6,8,-11⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source57.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source57.rootCodes link57 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual57_006
namespace C13.Global.FastDual57_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,5,7,11]
def points : Finset C13.Point := {2,5,7,11}
def columns : List Code := [638,731,829,830,859,892,923,971,979,1371,1447,1453,1461,1509,1627,1639,1646,1654,1691,1739,1753,1819,1831,1837,1838,1845,1846,1852,1867,1875,1881,1882,1893,1894,1900,1908,1931,1939,1945,1957,1987,1993,2001,2171,2270,2363,2411,2425,2455,2462,2518,2619,2647,2653,2667,2731,2746,2794,2839,2859,2901,2921,2966,2986,3131,3179,3187,3277,3278,3292,3371,3379,3433,3441,3470,3478,3532,3540,3627,3635,3661,3669,3754,3788]
def rows : List LinearRow := [⟨.covers 163,1,1⟩,⟨.covers 57,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 226,1,2⟩,⟨.covers 172,1,2⟩,⟨.covers 2316,1,1⟩,⟨.covers 180,1,2⟩,⟨.covers 228,1,2⟩,⟨.covers 1584,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 928,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 3712,1,1⟩,⟨.incident 5,8,-1⟩,⟨.incident 7,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source57.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source57.rootCodes link57 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual57_007
