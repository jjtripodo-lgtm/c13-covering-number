import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source40
namespace C13.Global.FastDual40_032
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,8,9]
def points : Finset C13.Point := {2,3,8,9}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,829,830,892,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1401,1402,1447,1461,1462,1491,1498,1507,1509,1521,1522,1524,1528,1639,1653,1654,1691,1721,1722,1747,1753,1763,1766,1777,1778,1780,1784,1852,1987,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2425,2426,2455,2485,2486,2515,2518,2531,2537,2545,2546,2548,2552,2647,2677,2678,2731,2745,2746,2771,2773,2787,2794,2801,2802,2804,2808,2876,3011,3056,3187,3251,3271,3275,3277,3278,3283,3285,3286,3289,3290,3292,3299,3301,3302,3305,3306,3308,3313,3314,3316,3320,3403,3418,3433,3448,3463,3478,3493,3508,3523,3538,3553,3568,3655,3669,3686,3700,3723,3737,3754,3768,3779,3793,3810,3824]
def rows : List LinearRow := [⟨.covers 519,1,1⟩,⟨.covers 523,1,1⟩,⟨.covers 269,1,2⟩,⟨.covers 1037,1,1⟩,⟨.covers 1541,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 270,1,2⟩,⟨.covers 1038,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 1074,1,1⟩,⟨.covers 1794,1,2⟩,⟨.covers 2818,1,2⟩,⟨.covers 92,1,1⟩,⟨.covers 1292,1,2⟩,⟨.covers 2316,1,2⟩,⟨.covers 864,1,1⟩,⟨.covers 3616,1,1⟩,⟨.incident 9,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_032
namespace C13.Global.FastDual40_033
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,8]
def points : Finset C13.Point := {2,6,7,8}
def columns : List Code := [379,439,631,699,829,830,859,875,971,979,995,1371,1387,1402,1447,1453,1461,1595,1639,1646,1654,1691,1707,1721,1837,1852,1867,1882,1957,1987,2395,2411,2425,2455,2462,2486,2619,2647,2653,2677,2715,2731,2746,2846,2876,2891,2921,2966,3011,3131,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3611,3627,3635,3641,3642,3655,3661,3662,3669,3670,3676,3685,3686,3692,3700,3723,3737,3738,3753,3754,3768,3788,3854,3884,3914,3944,3974,4004,4034,4064]
def rows : List LinearRow := [⟨.covers 139,1,6⟩,⟨.covers 197,1,6⟩,⟨.covers 2309,1,25⟩,⟨.covers 169,1,6⟩,⟨.covers 201,1,19⟩,⟨.covers 1665,1,6⟩,⟨.covers 166,1,25⟩,⟨.covers 198,1,25⟩,⟨.covers 154,1,6⟩,⟨.covers 210,1,25⟩,⟨.covers 226,1,25⟩,⟨.covers 156,1,19⟩,⟨.covers 172,1,19⟩,⟨.covers 212,1,6⟩,⟨.covers 228,1,6⟩,⟨.covers 184,1,6⟩,⟨.covers 1672,1,6⟩,⟨.covers 2696,1,6⟩,⟨.covers 1424,1,25⟩,⟨.covers 2704,1,6⟩,⟨.covers 2496,1,6⟩,⟨.covers 1920,1,19⟩,⟨.incident 7,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_033
namespace C13.Global.FastDual40_034
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,9]
def points : Finset C13.Point := {2,6,7,9}
def columns : List Code := [379,439,631,699,829,830,923,939,971,979,995,1339,1371,1387,1402,1447,1453,1461,1639,1646,1654,1691,1707,1721,1838,1852,1894,1931,1945,1987,2363,2395,2411,2425,2455,2462,2486,2647,2653,2677,2715,2731,2746,2845,2876,2901,2955,2986,3011,3131,3277,3278,3292,3308,3355,3371,3379,3385,3386,3403,3417,3418,3433,3434,3448,3463,3469,3470,3477,3478,3484,3493,3494,3500,3508,3532,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,2⟩,⟨.covers 75,1,5⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,4⟩,⟨.covers 1061,1,1⟩,⟨.covers 197,1,19⟩,⟨.covers 1541,1,10⟩,⟨.covers 89,1,5⟩,⟨.covers 169,1,3⟩,⟨.covers 777,1,1⟩,⟨.covers 2145,1,4⟩,⟨.covers 2337,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 86,1,11⟩,⟨.covers 2070,1,2⟩,⟨.covers 166,1,2⟩,⟨.covers 198,1,19⟩,⟨.covers 154,1,2⟩,⟨.covers 1050,1,1⟩,⟨.covers 106,1,5⟩,⟨.covers 210,1,19⟩,⟨.covers 1106,1,4⟩,⟨.covers 226,1,19⟩,⟨.covers 2594,1,2⟩,⟨.covers 92,1,10⟩,⟨.covers 156,1,1⟩,⟨.covers 108,1,9⟩,⟨.covers 172,1,1⟩,⟨.covers 212,1,8⟩,⟨.covers 228,1,9⟩,⟨.covers 3332,1,1⟩,⟨.covers 3588,1,5⟩,⟨.covers 1560,1,1⟩,⟨.covers 3592,1,2⟩,⟨.covers 2384,1,5⟩,⟨.covers 1424,1,3⟩,⟨.covers 2704,1,1⟩,⟨.covers 1376,1,5⟩,⟨.covers 2656,1,8⟩,⟨.covers 2464,1,2⟩,⟨.covers 1696,1,1⟩,⟨.covers 2848,1,1⟩,⟨.covers 1472,1,4⟩,⟨.covers 2496,1,9⟩,⟨.covers 1728,1,5⟩,⟨.covers 1856,1,10⟩,⟨.covers 2880,1,10⟩,⟨.covers 3392,1,5⟩,⟨.incident 6,8,-14⟩,⟨.incident 7,8,-4⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_034
namespace C13.Global.FastDual40_035
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,11]
def points : Finset C13.Point := {2,6,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,859,875,883,923,939,947,971,979,995,1339,1371,1387,1402,1447,1453,1461,1595,1639,1646,1654,1691,1707,1721,1819,1831,1835,1837,1838,1843,1845,1846,1849,1850,1852,1867,1875,1882,1891,1894,1898,1906,1931,1939,1945,1955,1957,1961,1969,1987,2363,2411,2425,2455,2462,2486,2619,2647,2653,2677,2731,2746,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3277,3278,3292,3308,3371,3379,3433,3470,3478,3532,3627,3635,3661,3669,3754,3788]
def rows : List LinearRow := [⟨.covers 135,1,3⟩,⟨.covers 1031,1,8⟩,⟨.covers 2055,1,8⟩,⟨.covers 75,1,6⟩,⟨.covers 139,1,6⟩,⟨.covers 2059,1,3⟩,⟨.covers 141,1,8⟩,⟨.covers 525,1,8⟩,⟨.covers 101,1,3⟩,⟨.covers 197,1,3⟩,⟨.covers 1049,1,3⟩,⟨.covers 169,1,3⟩,⟨.covers 270,1,8⟩,⟨.covers 86,1,3⟩,⟨.covers 198,1,11⟩,⟨.covers 1050,1,3⟩,⟨.covers 106,1,3⟩,⟨.covers 210,1,11⟩,⟨.covers 3090,1,3⟩,⟨.covers 226,1,11⟩,⟨.covers 3330,1,3⟩,⟨.covers 3586,1,8⟩,⟨.covers 156,1,3⟩,⟨.covers 540,1,3⟩,⟨.covers 108,1,8⟩,⟨.covers 116,1,6⟩,⟨.covers 180,1,8⟩,⟨.covers 212,1,8⟩,⟨.covers 228,1,3⟩,⟨.covers 1796,1,3⟩,⟨.covers 2820,1,3⟩,⟨.covers 120,1,3⟩,⟨.covers 184,1,3⟩,⟨.covers 2824,1,8⟩,⟨.covers 2384,1,8⟩,⟨.covers 1616,1,3⟩,⟨.covers 1424,1,3⟩,⟨.covers 2704,1,8⟩,⟨.covers 1376,1,3⟩,⟨.covers 2656,1,3⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,3⟩,⟨.covers 3360,1,6⟩,⟨.covers 2496,1,11⟩,⟨.covers 2752,1,11⟩,⟨.covers 1856,1,6⟩,⟨.covers 1920,1,6⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_035
namespace C13.Global.FastDual40_036
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,8,9]
def points : Finset C13.Point := {2,6,8,9}
def columns : List Code := [254,379,439,445,446,475,491,506,631,699,758,829,830,956,971,979,995,1010,1211,1262,1371,1387,1402,1447,1453,1461,1462,1468,1483,1498,1639,1646,1654,1691,1707,1721,1722,1766,1852,1987,2235,2269,2300,2395,2411,2425,2455,2462,2485,2486,2492,2507,2537,2552,2647,2653,2677,2715,2731,2745,2746,2773,2804,2876,3011,3056,3131,3227,3243,3251,3257,3258,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 1037,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 773,1,1⟩,⟨.covers 2062,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 1616,1,1⟩,⟨.incident 2,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_036
namespace C13.Global.FastDual40_037
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,8,11]
def points : Finset C13.Point := {2,6,8,11}
def columns : List Code := [254,379,439,445,446,475,491,506,631,699,758,829,830,859,875,949,950,956,971,979,995,1010,1211,1262,1371,1387,1402,1447,1453,1461,1462,1468,1483,1498,1595,1639,1646,1654,1691,1707,1715,1721,1722,1766,1837,1852,1867,1882,1957,1972,1987,2002,2235,2269,2300,2411,2425,2455,2462,2486,2537,2552,2619,2647,2653,2677,2731,2739,2746,2773,2804,2921,2966,3056,3131,3243,3251,3258,3277,3278,3292,3308,3433,3478,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 197,1,2⟩,⟨.covers 2309,1,1⟩,⟨.covers 2097,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 2314,1,2⟩,⟨.covers 3082,1,1⟩,⟨.covers 2818,1,2⟩,⟨.covers 3330,1,1⟩,⟨.covers 2572,1,2⟩,⟨.covers 2824,1,2⟩,⟨.covers 3336,1,1⟩,⟨.covers 3152,1,2⟩,⟨.covers 3168,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 2496,1,2⟩,⟨.incident 11,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_037
namespace C13.Global.FastDual40_038
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,9,11]
def points : Finset C13.Point := {2,6,9,11}
def columns : List Code := [254,379,439,443,445,446,475,491,506,631,699,758,829,830,923,939,953,954,956,971,979,995,1010,1211,1262,1339,1371,1387,1402,1435,1447,1451,1453,1454,1459,1461,1462,1465,1466,1468,1483,1498,1514,1639,1646,1654,1691,1707,1721,1722,1766,1838,1852,1894,1931,1945,1962,1976,1987,2018,2235,2269,2300,2363,2411,2425,2455,2462,2475,2483,2486,2490,2537,2552,2647,2653,2677,2731,2746,2773,2804,2901,2986,3056,3131,3243,3251,3258,3277,3278,3292,3308,3371,3379,3433,3470,3478,3498,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 135,1,8⟩,⟨.covers 523,1,9⟩,⟨.covers 2059,1,8⟩,⟨.covers 1043,1,2⟩,⟨.covers 2307,1,5⟩,⟨.covers 269,1,8⟩,⟨.covers 101,1,13⟩,⟨.covers 197,1,13⟩,⟨.covers 1049,1,2⟩,⟨.covers 777,1,5⟩,⟨.covers 2569,1,2⟩,⟨.covers 526,1,9⟩,⟨.covers 198,1,7⟩,⟨.covers 1094,1,1⟩,⟨.covers 774,1,4⟩,⟨.covers 2566,1,19⟩,⟨.covers 210,1,1⟩,⟨.covers 1106,1,1⟩,⟨.covers 2818,1,19⟩,⟨.covers 3586,1,19⟩,⟨.covers 2316,1,13⟩,⟨.covers 2572,1,17⟩,⟨.covers 564,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 2820,1,19⟩,⟨.covers 3588,1,19⟩,⟨.covers 1112,1,2⟩,⟨.covers 368,1,5⟩,⟨.covers 1584,1,12⟩,⟨.covers 464,1,2⟩,⟨.covers 1424,1,2⟩,⟨.covers 3216,1,11⟩,⟨.covers 2656,1,5⟩,⟨.covers 3168,1,13⟩,⟨.covers 1728,1,6⟩,⟨.covers 2752,1,6⟩,⟨.covers 1856,1,8⟩,⟨.incident 9,8,-6⟩,⟨.incident 11,8,-5⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_038
namespace C13.Global.FastDual40_039
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,8,9]
def points : Finset C13.Point := {2,7,8,9}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,892,971,979,995,1147,1261,1371,1387,1401,1402,1447,1453,1461,1509,1639,1646,1653,1654,1660,1691,1707,1721,1739,1753,1852,1987,2171,2270,2395,2411,2425,2426,2455,2462,2486,2518,2647,2653,2677,2678,2684,2715,2731,2746,2763,2794,2876,3011,3131,3163,3179,3187,3193,3194,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 71,1,5⟩,⟨.covers 139,1,1⟩,⟨.covers 267,1,4⟩,⟨.covers 269,1,6⟩,⟨.covers 2061,1,5⟩,⟨.covers 101,1,3⟩,⟨.covers 2309,1,12⟩,⟨.covers 169,1,2⟩,⟨.covers 777,1,11⟩,⟨.covers 1289,1,4⟩,⟨.covers 2569,1,4⟩,⟨.covers 2145,1,4⟩,⟨.covers 1038,1,5⟩,⟨.covers 166,1,12⟩,⟨.covers 774,1,16⟩,⟨.covers 2566,1,4⟩,⟨.covers 1050,1,4⟩,⟨.covers 2314,1,4⟩,⟨.covers 1546,1,3⟩,⟨.covers 1570,1,2⟩,⟨.covers 2594,1,1⟩,⟨.covers 1794,1,8⟩,⟨.covers 2818,1,7⟩,⟨.covers 156,1,5⟩,⟨.covers 1796,1,16⟩,⟨.covers 2820,1,16⟩,⟨.covers 184,1,5⟩,⟨.covers 368,1,4⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,6⟩,⟨.covers 912,1,15⟩,⟨.covers 1424,1,12⟩,⟨.covers 2704,1,3⟩,⟨.covers 2272,1,5⟩,⟨.covers 1376,1,4⟩,⟨.covers 2656,1,3⟩,⟨.covers 928,1,15⟩,⟨.covers 1696,1,1⟩,⟨.covers 1472,1,6⟩,⟨.covers 2496,1,9⟩,⟨.covers 1728,1,2⟩,⟨.incident 2,8,-1⟩,⟨.incident 8,8,-7⟩,⟨.incident 9,8,-4⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_039
