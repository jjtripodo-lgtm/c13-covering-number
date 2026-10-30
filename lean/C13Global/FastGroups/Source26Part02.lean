import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source26
namespace C13.Global.FastDual26_016
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,10,11]
def points : Finset C13.Point := {2,3,10,11}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,823,827,829,830,883,885,886,889,890,892,947,949,950,953,954,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1395,1402,1447,1459,1461,1497,1498,1509,1510,1521,1522,1524,1528,1639,1651,1654,1691,1715,1721,1753,1754,1765,1766,1777,1778,1780,1784,1819,1831,1843,1882,1894,1906,1945,1957,1969,2008,2020,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2419,2425,2455,2483,2486,2517,2518,2537,2538,2545,2546,2548,2552,2647,2675,2677,2731,2739,2746,2773,2774,2793,2794,2801,2802,2804,2808,2839,2859,2867,2901,2921,2929,2966,2986,2994,3028,3048,3056,3187,3251,3277,3278,3292,3308,3313,3314,3316,3320,3379,3532,3568,3635,3788,3824]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 135,1,2⟩,⟨.covers 1031,1,5⟩,⟨.covers 2055,1,2⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,8⟩,⟨.covers 1035,1,2⟩,⟨.covers 2059,1,4⟩,⟨.covers 269,1,19⟩,⟨.covers 1037,1,19⟩,⟨.covers 149,1,3⟩,⟨.covers 101,1,1⟩,⟨.covers 2309,1,11⟩,⟨.covers 1541,1,5⟩,⟨.covers 89,1,3⟩,⟨.covers 169,1,2⟩,⟨.covers 1289,1,10⟩,⟨.covers 2569,1,5⟩,⟨.covers 1169,1,1⟩,⟨.covers 2145,1,4⟩,⟨.covers 1185,1,4⟩,⟨.covers 705,1,9⟩,⟨.covers 270,1,19⟩,⟨.covers 1038,1,19⟩,⟨.covers 86,1,3⟩,⟨.covers 1286,1,5⟩,⟨.covers 2566,1,5⟩,⟨.covers 154,1,1⟩,⟨.covers 2314,1,5⟩,⟨.covers 1546,1,6⟩,⟨.covers 114,1,2⟩,⟨.covers 178,1,2⟩,⟨.covers 1106,1,1⟩,⟨.covers 2194,1,2⟩,⟨.covers 1122,1,1⟩,⟨.covers 450,1,9⟩,⟨.covers 706,1,2⟩,⟨.covers 3330,1,19⟩,⟨.covers 3586,1,19⟩,⟨.covers 92,1,1⟩,⟨.covers 156,1,2⟩,⟨.covers 172,1,8⟩,⟨.covers 1292,1,19⟩,⟨.covers 1548,1,19⟩,⟨.covers 596,1,1⟩,⟨.covers 2132,1,2⟩,⟨.covers 612,1,1⟩,⟨.covers 420,1,3⟩,⟨.covers 1796,1,5⟩,⟨.covers 2820,1,1⟩,⟨.covers 1112,1,3⟩,⟨.covers 664,1,1⟩,⟨.covers 360,1,5⟩,⟨.covers 1800,1,1⟩,⟨.covers 2824,1,5⟩,⟨.covers 688,1,4⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,2⟩,⟨.covers 1424,1,3⟩,⟨.covers 2704,1,2⟩,⟨.covers 1376,1,1⟩,⟨.covers 3168,1,11⟩,⟨.covers 1856,1,6⟩,⟨.covers 1920,1,3⟩,⟨.covers 2944,1,9⟩]
def bound : Int := 20

theorem column_mask : listMask columns = restrictMask universeMask Source26.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source26.rootCodes link26 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual26_016
namespace C13.Global.FastDual26_017
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,9]
def points : Finset C13.Point := {2,6,7,9}
def columns : List Code := [379,439,631,699,829,830,923,939,971,979,995,1339,1371,1387,1402,1447,1453,1461,1639,1646,1654,1691,1707,1721,1838,1852,1894,1931,1945,1987,2363,2395,2411,2425,2455,2462,2486,2647,2653,2677,2715,2731,2746,2845,2876,2901,2955,2986,3011,3131,3277,3278,3292,3308,3355,3371,3379,3385,3386,3403,3417,3418,3433,3434,3448,3463,3469,3470,3477,3478,3484,3493,3494,3500,3508,3532,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,3⟩,⟨.covers 75,1,5⟩,⟨.covers 139,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 197,1,6⟩,⟨.covers 773,1,2⟩,⟨.covers 1541,1,14⟩,⟨.covers 89,1,5⟩,⟨.covers 169,1,3⟩,⟨.covers 201,1,12⟩,⟨.covers 1169,1,1⟩,⟨.covers 2145,1,2⟩,⟨.covers 1185,1,1⟩,⟨.covers 2337,1,2⟩,⟨.covers 78,1,9⟩,⟨.covers 86,1,11⟩,⟨.covers 2070,1,2⟩,⟨.covers 166,1,2⟩,⟨.covers 198,1,9⟩,⟨.covers 154,1,2⟩,⟨.covers 1050,1,2⟩,⟨.covers 106,1,5⟩,⟨.covers 210,1,17⟩,⟨.covers 1106,1,2⟩,⟨.covers 226,1,9⟩,⟨.covers 2594,1,2⟩,⟨.covers 92,1,9⟩,⟨.covers 156,1,2⟩,⟨.covers 172,1,2⟩,⟨.covers 212,1,7⟩,⟨.covers 228,1,16⟩,⟨.covers 3332,1,1⟩,⟨.covers 1800,1,2⟩,⟨.covers 3592,1,3⟩,⟨.covers 848,1,1⟩,⟨.covers 2384,1,5⟩,⟨.covers 1424,1,3⟩,⟨.covers 2704,1,2⟩,⟨.covers 864,1,9⟩,⟨.covers 1376,1,5⟩,⟨.covers 2656,1,11⟩,⟨.covers 2464,1,2⟩,⟨.covers 1696,1,1⟩,⟨.covers 2848,1,2⟩,⟨.covers 2496,1,12⟩,⟨.covers 1728,1,18⟩,⟨.covers 2880,1,6⟩,⟨.covers 3392,1,5⟩,⟨.incident 6,8,-11⟩,⟨.incident 7,8,-5⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source26.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source26.rootCodes link26 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual26_017
namespace C13.Global.FastDual26_018
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,10]
def points : Finset C13.Point := {2,6,7,10}
def columns : List Code := [379,439,631,699,823,827,829,830,859,875,883,923,939,947,971,979,995,1339,1371,1402,1447,1453,1461,1595,1639,1646,1654,1691,1721,1819,1831,1843,1882,1894,1906,1945,1957,1969,2363,2395,2411,2425,2455,2462,2486,2619,2647,2653,2677,2715,2731,2746,2839,2843,2845,2846,2859,2867,2869,2870,2873,2874,2876,2891,2899,2901,2905,2915,2921,2929,2955,2963,2966,2970,2979,2986,2994,3011,3131,3277,3278,3292,3308,3355,3379,3418,3469,3493,3532,3611,3635,3662,3686,3737,3788]
def rows : List LinearRow := [⟨.covers 2055,1,11⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,3⟩,⟨.covers 1035,1,8⟩,⟨.covers 2059,1,3⟩,⟨.covers 77,1,6⟩,⟨.covers 269,1,7⟩,⟨.covers 525,1,3⟩,⟨.covers 101,1,11⟩,⟨.covers 197,1,5⟩,⟨.covers 89,1,1⟩,⟨.covers 169,1,3⟩,⟨.covers 78,1,4⟩,⟨.covers 270,1,11⟩,⟨.covers 166,1,3⟩,⟨.covers 1286,1,8⟩,⟨.covers 106,1,5⟩,⟨.covers 202,1,7⟩,⟨.covers 210,1,11⟩,⟨.covers 226,1,11⟩,⟨.covers 1548,1,2⟩,⟨.covers 180,1,8⟩,⟨.covers 212,1,11⟩,⟨.covers 228,1,11⟩,⟨.covers 1796,1,3⟩,⟨.covers 120,1,3⟩,⟨.covers 184,1,5⟩,⟨.covers 2344,1,2⟩,⟨.covers 2600,1,2⟩,⟨.covers 1800,1,3⟩,⟨.covers 1136,1,3⟩,⟨.covers 1200,1,3⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,8⟩,⟨.covers 2704,1,4⟩,⟨.covers 2848,1,1⟩,⟨.covers 3360,1,11⟩,⟨.covers 3616,1,11⟩,⟨.covers 1472,1,4⟩,⟨.covers 1728,1,2⟩,⟨.covers 2880,1,5⟩,⟨.covers 3392,1,7⟩,⟨.covers 1920,1,8⟩,⟨.covers 2944,1,5⟩,⟨.covers 3712,1,7⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source26.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source26.rootCodes link26 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual26_018
namespace C13.Global.FastDual26_019
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,11]
def points : Finset C13.Point := {2,6,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,859,875,883,923,939,947,971,979,995,1339,1371,1387,1402,1447,1453,1461,1595,1639,1646,1654,1691,1707,1721,1819,1831,1835,1837,1838,1843,1845,1846,1849,1850,1852,1867,1875,1882,1891,1894,1898,1906,1931,1939,1945,1955,1957,1961,1969,1987,2363,2411,2425,2455,2462,2486,2619,2647,2653,2677,2731,2746,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3277,3278,3292,3308,3371,3379,3433,3470,3478,3532,3627,3635,3661,3669,3754,3788]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 1031,1,8⟩,⟨.covers 75,1,6⟩,⟨.covers 139,1,6⟩,⟨.covers 2059,1,4⟩,⟨.covers 141,1,8⟩,⟨.covers 269,1,1⟩,⟨.covers 525,1,8⟩,⟨.covers 149,1,7⟩,⟨.covers 197,1,1⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 1049,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 78,1,10⟩,⟨.covers 270,1,10⟩,⟨.covers 86,1,10⟩,⟨.covers 166,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 1050,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 210,1,11⟩,⟨.covers 3090,1,4⟩,⟨.covers 226,1,11⟩,⟨.covers 3586,1,7⟩,⟨.covers 540,1,1⟩,⟨.covers 180,1,3⟩,⟨.covers 212,1,7⟩,⟨.covers 228,1,11⟩,⟨.covers 2820,1,7⟩,⟨.covers 120,1,3⟩,⟨.covers 184,1,3⟩,⟨.covers 1304,1,1⟩,⟨.covers 1560,1,1⟩,⟨.covers 2824,1,7⟩,⟨.covers 2160,1,7⟩,⟨.covers 2224,1,7⟩,⟨.covers 1616,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 3216,1,4⟩,⟨.covers 1376,1,4⟩,⟨.covers 2656,1,4⟩,⟨.covers 1696,1,4⟩,⟨.covers 3360,1,7⟩,⟨.covers 2496,1,11⟩,⟨.covers 2752,1,11⟩,⟨.covers 1856,1,6⟩,⟨.covers 1920,1,6⟩,⟨.covers 2944,1,4⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source26.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source26.rootCodes link26 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual26_019
namespace C13.Global.FastDual26_020
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,9,10]
def points : Finset C13.Point := {2,6,9,10}
def columns : List Code := [379,439,443,445,446,475,491,631,699,829,830,923,939,953,954,956,971,979,995,1211,1262,1339,1371,1402,1435,1447,1453,1459,1461,1465,1498,1639,1646,1654,1691,1721,1766,1894,1945,2235,2269,2363,2395,2411,2425,2455,2459,2461,2462,2475,2483,2485,2486,2489,2490,2492,2507,2521,2537,2647,2653,2677,2715,2731,2745,2746,2773,2845,2876,2901,2955,2969,2986,3000,3011,3025,3131,3227,3251,3257,3277,3278,3292,3308,3355,3379,3418,3469,3481,3493,3505,3532,3544,3686,3737]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 523,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 197,1,1⟩,⟨.covers 1541,1,1⟩,⟨.covers 2062,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 2272,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 1728,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source26.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source26.rootCodes link26 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual26_020
namespace C13.Global.FastDual26_021
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,9,11]
def points : Finset C13.Point := {2,6,9,11}
def columns : List Code := [379,439,443,445,446,475,491,631,699,829,830,923,939,953,954,956,971,979,995,1211,1262,1339,1371,1387,1402,1435,1447,1451,1453,1454,1459,1461,1462,1465,1466,1468,1483,1498,1514,1639,1646,1654,1691,1707,1721,1722,1766,1838,1852,1894,1931,1945,1962,1976,1987,2018,2235,2269,2363,2411,2425,2455,2462,2475,2483,2486,2490,2537,2647,2653,2677,2731,2746,2773,2901,2986,3131,3243,3251,3258,3277,3278,3292,3308,3371,3379,3433,3470,3478,3498,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3332,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 1232,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 736,1,1⟩,⟨.covers 2272,1,1⟩,⟨.covers 2656,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source26.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source26.rootCodes link26 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual26_021
namespace C13.Global.FastDual26_022
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,10,11]
def points : Finset C13.Point := {2,6,10,11}
def columns : List Code := [379,439,443,445,446,475,491,631,699,823,827,829,830,859,875,883,923,939,947,949,950,953,954,956,971,979,995,1211,1262,1339,1371,1402,1435,1447,1453,1459,1461,1465,1498,1595,1639,1646,1654,1691,1715,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2235,2269,2363,2411,2425,2455,2462,2475,2483,2486,2490,2537,2619,2647,2653,2677,2731,2739,2746,2773,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3251,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 135,1,6⟩,⟨.covers 2055,1,5⟩,⟨.covers 75,1,6⟩,⟨.covers 139,1,2⟩,⟨.covers 1035,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 269,1,4⟩,⟨.covers 525,1,7⟩,⟨.covers 1037,1,2⟩,⟨.covers 101,1,5⟩,⟨.covers 1541,1,6⟩,⟨.covers 3077,1,9⟩,⟨.covers 169,1,2⟩,⟨.covers 1289,1,3⟩,⟨.covers 2569,1,4⟩,⟨.covers 270,1,6⟩,⟨.covers 526,1,5⟩,⟨.covers 1286,1,5⟩,⟨.covers 2566,1,6⟩,⟨.covers 3078,1,10⟩,⟨.covers 2314,1,3⟩,⟨.covers 1546,1,6⟩,⟨.covers 210,1,2⟩,⟨.covers 3330,1,10⟩,⟨.covers 3586,1,10⟩,⟨.covers 2316,1,2⟩,⟨.covers 116,1,6⟩,⟨.covers 180,1,5⟩,⟨.covers 3588,1,10⟩,⟨.covers 120,1,4⟩,⟨.covers 664,1,2⟩,⟨.covers 680,1,2⟩,⟨.covers 1800,1,1⟩,⟨.covers 2824,1,3⟩,⟨.covers 1136,1,1⟩,⟨.covers 1200,1,5⟩,⟨.covers 2224,1,5⟩,⟨.covers 720,1,8⟩,⟨.covers 2384,1,6⟩,⟨.covers 1616,1,4⟩,⟨.covers 3152,1,10⟩,⟨.covers 2704,1,2⟩,⟨.covers 736,1,10⟩,⟨.covers 2272,1,8⟩,⟨.covers 1376,1,6⟩,⟨.covers 3168,1,2⟩,⟨.covers 1472,1,8⟩,⟨.covers 2880,1,4⟩,⟨.covers 1920,1,5⟩,⟨.covers 2944,1,3⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source26.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source26.rootCodes link26 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual26_022
namespace C13.Global.FastDual26_023
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,10]
def points : Finset C13.Point := {2,7,9,10}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1639,1646,1654,1691,1721,1753,1894,1945,2171,2270,2363,2395,2411,2419,2425,2426,2455,2462,2486,2518,2647,2653,2677,2678,2684,2715,2731,2746,2763,2794,2845,2876,2901,2932,2955,2986,3011,3042,3131,3163,3187,3194,3277,3278,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 1031,1,4⟩,⟨.covers 2055,1,6⟩,⟨.covers 139,1,2⟩,⟨.covers 1035,1,4⟩,⟨.covers 163,1,1⟩,⟨.covers 1283,1,4⟩,⟨.covers 1539,1,8⟩,⟨.covers 2563,1,2⟩,⟨.covers 525,1,5⟩,⟨.covers 197,1,14⟩,⟨.covers 773,1,2⟩,⟨.covers 1541,1,5⟩,⟨.covers 2097,1,4⟩,⟨.covers 833,1,1⟩,⟨.covers 2625,1,2⟩,⟨.covers 270,1,7⟩,⟨.covers 166,1,5⟩,⟨.covers 3078,1,11⟩,⟨.covers 330,1,4⟩,⟨.covers 3082,1,4⟩,⟨.covers 226,1,4⟩,⟨.covers 1794,1,17⟩,⟨.covers 2818,1,1⟩,⟨.covers 3586,1,6⟩,⟨.covers 1292,1,14⟩,⟨.covers 1548,1,17⟩,⟨.covers 2572,1,3⟩,⟨.covers 116,1,2⟩,⟨.covers 212,1,7⟩,⟨.covers 808,1,3⟩,⟨.covers 2600,1,2⟩,⟨.covers 1800,1,13⟩,⟨.covers 3592,1,13⟩,⟨.covers 1136,1,4⟩,⟨.covers 1200,1,11⟩,⟨.covers 2224,1,2⟩,⟨.covers 1328,1,4⟩,⟨.covers 1584,1,2⟩,⟨.covers 2608,1,3⟩,⟨.covers 1232,1,4⟩,⟨.covers 848,1,5⟩,⟨.covers 1616,1,10⟩,⟨.covers 3152,1,4⟩,⟨.covers 928,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 3232,1,14⟩,⟨.covers 2752,1,1⟩,⟨.incident 2,8,-4⟩,⟨.incident 9,8,-3⟩,⟨.incident 10,8,-7⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source26.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source26.rootCodes link26 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual26_023
