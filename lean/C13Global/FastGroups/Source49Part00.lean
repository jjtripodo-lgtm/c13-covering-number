import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source49
namespace C13.Global.FastDual49_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,8]
def points : Finset C13.Point := {1,3,6,8}
def columns : List Code := [254,506,701,743,758,829,949,956,967,979,995,1010,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1724,1766,1852,1882,1957,1972,1987,2002,2231,2285,2300,2413,2425,2455,2485,2486,2537,2552,2677,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2773,2789,2804,2861,2876,2921,2951,2966,2981,2996,3011,3041,3056,3127,3251,3253,3254,3277,3292,3308,3418,3433,3448,3478,3493,3508,3623,3635,3637,3638,3669,3685,3686,3700,3725,3733,3737,3740,3747,3749,3750,3753,3754,3756,3761,3762,3764,3768,3781,3788,3796,3812]
def rows : List LinearRow := [⟨.covers 75,1,2⟩,⟨.covers 139,1,2⟩,⟨.covers 147,1,1⟩,⟨.covers 2067,1,1⟩,⟨.covers 99,1,2⟩,⟨.covers 270,1,2⟩,⟨.covers 526,1,2⟩,⟨.covers 774,1,2⟩,⟨.covers 3078,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 114,1,2⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 1472,1,2⟩,⟨.incident 1,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source49.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source49.rootCodes link49 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual49_000
namespace C13.Global.FastDual49_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,9]
def points : Finset C13.Point := {1,3,6,9}
def columns : List Code := [254,506,701,743,758,829,953,956,967,979,995,1010,1371,1374,1402,1461,1498,1639,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2231,2285,2300,2413,2425,2455,2483,2485,2486,2537,2552,2677,2731,2734,2745,2746,2748,2773,2804,2876,2901,2986,3000,3011,3025,3056,3127,3251,3253,3254,3277,3292,3308,3351,3379,3381,3382,3405,3417,3418,3420,3433,3436,3448,3475,3477,3478,3493,3505,3506,3508,3529,3532,3544,3560,3669,3686,3700,3737,3754,3768,3851,3865,3882,3896,3907,3921,3938,3952]
def rows : List LinearRow := [⟨.covers 75,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 1728,1,1⟩,⟨.incident 1,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source49.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source49.rootCodes link49 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual49_001
namespace C13.Global.FastDual49_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,11]
def points : Finset C13.Point := {1,3,6,11}
def columns : List Code := [254,506,701,743,758,829,949,953,956,967,979,995,1010,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1724,1766,1821,1845,1849,1852,1863,1875,1878,1882,1891,1894,1906,1941,1945,1948,1957,1969,1972,1976,1987,1990,2002,2018,2231,2285,2300,2413,2425,2455,2483,2486,2537,2552,2677,2731,2734,2739,2742,2746,2773,2804,2901,2921,2929,2966,2986,2994,3056,3127,3251,3254,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 75,1,3⟩,⟨.covers 139,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 201,1,3⟩,⟨.covers 777,1,1⟩,⟨.covers 2569,1,2⟩,⟨.covers 270,1,3⟩,⟨.covers 526,1,3⟩,⟨.covers 154,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 2314,1,3⟩,⟨.covers 1546,1,2⟩,⟨.covers 2316,1,3⟩,⟨.covers 568,1,1⟩,⟨.covers 664,1,1⟩,⟨.covers 3168,1,3⟩,⟨.incident 3,8,-3⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source49.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source49.rootCodes link49 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual49_002
namespace C13.Global.FastDual49_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,9,11]
def points : Finset C13.Point := {1,3,9,11}
def columns : List Code := [247,251,253,254,381,471,499,501,502,505,506,508,701,743,755,757,758,761,762,764,829,885,892,953,956,967,979,981,995,998,1009,1010,1012,1016,1143,1245,1267,1269,1270,1273,1274,1276,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1491,1493,1494,1497,1498,1500,1509,1521,1522,1524,1528,1639,1653,1654,1693,1721,1724,1749,1753,1763,1766,1777,1778,1780,1784,1821,1852,1863,1877,1894,1908,1945,1976,1987,2001,2018,2032,2231,2285,2291,2293,2294,2297,2298,2300,2413,2421,2425,2455,2483,2486,2517,2518,2537,2540,2545,2546,2548,2552,2677,2731,2734,2746,2773,2794,2801,2802,2804,2808,2901,2986,3056,3127,3187,3189,3251,3254,3277,3285,3292,3305,3308,3313,3314,3316,3320,3351,3379,3405,3413,3433,3441,3478,3506,3532,3540,3560,3568,3669,3754,3824]
def rows : List LinearRow := [⟨.covers 135,1,7⟩,⟨.covers 519,1,4⟩,⟨.covers 2055,1,6⟩,⟨.covers 267,1,19⟩,⟨.covers 523,1,19⟩,⟨.covers 99,1,2⟩,⟨.covers 2307,1,1⟩,⟨.covers 1539,1,10⟩,⟨.covers 141,1,7⟩,⟨.covers 525,1,6⟩,⟨.covers 2061,1,2⟩,⟨.covers 201,1,7⟩,⟨.covers 777,1,7⟩,⟨.covers 3081,1,2⟩,⟨.covers 2097,1,5⟩,⟨.covers 657,1,1⟩,⟨.covers 2145,1,2⟩,⟨.covers 417,1,8⟩,⟨.covers 705,1,1⟩,⟨.covers 1409,1,2⟩,⟨.covers 2817,1,19⟩,⟨.covers 3585,1,19⟩,⟨.covers 270,1,19⟩,⟨.covers 526,1,19⟩,⟨.covers 198,1,4⟩,⟨.covers 774,1,3⟩,⟨.covers 3078,1,8⟩,⟨.covers 154,1,4⟩,⟨.covers 106,1,6⟩,⟨.covers 778,1,19⟩,⟨.covers 1546,1,19⟩,⟨.covers 1074,1,1⟩,⟨.covers 402,1,4⟩,⟨.covers 2194,1,1⟩,⟨.covers 1122,1,2⟩,⟨.covers 1794,1,2⟩,⟨.covers 3330,1,5⟩,⟨.covers 108,1,1⟩,⟨.covers 2316,1,14⟩,⟨.covers 1548,1,1⟩,⟨.covers 116,1,5⟩,⟨.covers 564,1,3⟩,⟨.covers 2196,1,1⟩,⟨.covers 612,1,1⟩,⟨.covers 420,1,2⟩,⟨.covers 1188,1,8⟩,⟨.covers 568,1,3⟩,⟨.covers 1176,1,4⟩,⟨.covers 2152,1,1⟩,⟨.covers 1224,1,2⟩,⟨.covers 2248,1,1⟩,⟨.covers 1800,1,5⟩,⟨.covers 3336,1,2⟩,⟨.covers 464,1,5⟩,⟨.covers 2704,1,10⟩,⟨.covers 3216,1,1⟩,⟨.covers 864,1,4⟩,⟨.covers 3168,1,5⟩,⟨.covers 1824,1,7⟩,⟨.covers 3360,1,8⟩,⟨.covers 1728,1,3⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source49.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source49.rootCodes link49 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual49_003
namespace C13.Global.FastDual49_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,8,9]
def points : Finset C13.Point := {1,6,8,9}
def columns : List Code := [254,445,475,506,701,743,758,829,956,967,971,979,995,1010,1150,1213,1341,1371,1374,1402,1453,1461,1468,1498,1597,1639,1646,1654,1693,1721,1724,1766,1852,1987,2173,2231,2235,2237,2238,2269,2285,2300,2365,2413,2425,2455,2462,2477,2485,2486,2492,2537,2552,2621,2653,2677,2717,2731,2734,2745,2746,2748,2773,2804,2876,3011,3056,3127,3131,3133,3134,3165,3181,3196,3229,3245,3251,3253,3254,3257,3258,3260,3277,3292,3308,3358,3373,3388,3418,3433,3448,3478,3493,3508,3613,3630,3644,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 2055,1,7⟩,⟨.covers 2059,1,7⟩,⟨.covers 83,1,11⟩,⟨.covers 99,1,13⟩,⟨.covers 269,1,8⟩,⟨.covers 525,1,7⟩,⟨.covers 1157,1,3⟩,⟨.covers 2309,1,5⟩,⟨.covers 89,1,1⟩,⟨.covers 1161,1,3⟩,⟨.covers 777,1,5⟩,⟨.covers 2569,1,6⟩,⟨.covers 1793,1,20⟩,⟨.covers 2817,1,20⟩,⟨.covers 3585,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 270,1,9⟩,⟨.covers 526,1,5⟩,⟨.covers 1094,1,1⟩,⟨.covers 774,1,20⟩,⟨.covers 2566,1,8⟩,⟨.covers 1098,1,1⟩,⟨.covers 778,1,15⟩,⟨.covers 2314,1,3⟩,⟨.covers 1546,1,1⟩,⟨.covers 114,1,3⟩,⟨.covers 402,1,1⟩,⟨.covers 674,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 212,1,2⟩,⟨.covers 1220,1,2⟩,⟨.covers 664,1,1⟩,⟨.covers 1176,1,1⟩,⟨.covers 1800,1,20⟩,⟨.covers 2824,1,20⟩,⟨.covers 2256,1,1⟩,⟨.covers 1616,1,9⟩,⟨.covers 912,1,9⟩,⟨.covers 1424,1,10⟩,⟨.covers 3216,1,1⟩,⟨.covers 2272,1,3⟩,⟨.covers 864,1,6⟩,⟨.covers 1376,1,4⟩,⟨.covers 2656,1,1⟩,⟨.covers 1696,1,10⟩,⟨.covers 3232,1,2⟩,⟨.covers 3392,1,9⟩,⟨.covers 3648,1,4⟩,⟨.incident 8,8,-6⟩,⟨.incident 9,8,-7⟩]
def bound : Int := 8

theorem column_mask : listMask columns = restrictMask universeMask Source49.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source49.rootCodes link49 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual49_004
namespace C13.Global.FastDual49_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,8,11]
def points : Finset C13.Point := {1,6,8,11}
def columns : List Code := [254,445,475,506,701,743,758,829,941,949,956,967,971,979,995,1010,1150,1213,1341,1371,1374,1402,1453,1461,1468,1498,1597,1639,1646,1654,1693,1709,1717,1721,1724,1766,1837,1852,1867,1882,1957,1972,1987,2002,2173,2231,2235,2238,2269,2285,2300,2413,2425,2455,2462,2486,2537,2552,2653,2669,2677,2731,2734,2739,2742,2746,2765,2773,2804,2921,2966,3056,3127,3131,3165,3181,3251,3254,3258,3277,3292,3308,3433,3478,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 83,1,25⟩,⟨.covers 2307,1,25⟩,⟨.covers 269,1,6⟩,⟨.covers 773,1,6⟩,⟨.covers 417,1,6⟩,⟨.covers 2817,1,25⟩,⟨.covers 3329,1,25⟩,⟨.covers 774,1,19⟩,⟨.covers 1286,1,19⟩,⟨.covers 778,1,25⟩,⟨.covers 2314,1,6⟩,⟨.covers 2818,1,6⟩,⟨.covers 3330,1,6⟩,⟨.covers 1292,1,6⟩,⟨.covers 2316,1,19⟩,⟨.covers 308,1,6⟩,⟨.covers 420,1,6⟩,⟨.covers 1328,1,6⟩,⟨.covers 2384,1,6⟩,⟨.covers 1824,1,6⟩,⟨.covers 1472,1,25⟩,⟨.covers 2496,1,19⟩,⟨.incident 8,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source49.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source49.rootCodes link49 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual49_005
namespace C13.Global.FastDual49_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,9,11]
def points : Finset C13.Point := {1,6,9,11}
def columns : List Code := [254,445,475,506,701,743,758,829,925,953,956,967,971,979,995,1010,1150,1213,1341,1371,1374,1402,1437,1453,1461,1465,1468,1498,1597,1639,1646,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2173,2231,2235,2238,2269,2285,2300,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2552,2653,2677,2731,2734,2746,2773,2804,2901,2986,3056,3127,3131,3165,3181,3251,3254,3258,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 99,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 1584,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 1728,1,1⟩,⟨.incident 9,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source49.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source49.rootCodes link49 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual49_006
namespace C13.Global.FastDual49_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,8,9]
def points : Finset C13.Point := {3,6,8,9}
def columns : List Code := [254,379,439,506,631,699,701,702,727,743,758,829,830,956,967,979,995,1010,1207,1246,1371,1374,1402,1431,1447,1461,1462,1498,1623,1639,1654,1691,1693,1721,1722,1724,1735,1766,1852,1987,2231,2285,2300,2411,2413,2425,2455,2471,2485,2486,2537,2552,2647,2663,2677,2731,2734,2745,2746,2748,2759,2773,2804,2876,3011,3056,3127,3223,3239,3251,3253,3254,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 139,1,8⟩,⟨.covers 1037,1,11⟩,⟨.covers 101,1,3⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,1⟩,⟨.covers 89,1,20⟩,⟨.covers 169,1,5⟩,⟨.covers 201,1,9⟩,⟨.covers 777,1,20⟩,⟨.covers 2569,1,5⟩,⟨.covers 593,1,1⟩,⟨.covers 657,1,3⟩,⟨.covers 2577,1,3⟩,⟨.covers 417,1,3⟩,⟨.covers 1793,1,7⟩,⟨.covers 2817,1,7⟩,⟨.covers 270,1,14⟩,⟨.covers 1038,1,1⟩,⟨.covers 2062,1,19⟩,⟨.covers 774,1,4⟩,⟨.covers 1286,1,3⟩,⟨.covers 778,1,3⟩,⟨.covers 2314,1,20⟩,⟨.covers 1546,1,4⟩,⟨.covers 2098,1,7⟩,⟨.covers 2594,1,1⟩,⟨.covers 92,1,3⟩,⟨.covers 2316,1,14⟩,⟨.covers 216,1,15⟩,⟨.covers 664,1,4⟩,⟨.covers 1176,1,1⟩,⟨.covers 232,1,3⟩,⟨.covers 1800,1,20⟩,⟨.covers 2824,1,7⟩,⟨.covers 3592,1,3⟩,⟨.covers 1616,1,1⟩,⟨.covers 912,1,3⟩,⟨.covers 1424,1,4⟩,⟨.covers 864,1,4⟩,⟨.covers 1376,1,20⟩,⟨.covers 1696,1,7⟩,⟨.covers 3616,1,5⟩,⟨.incident 3,8,-14⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source49.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source49.rootCodes link49 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual49_007
