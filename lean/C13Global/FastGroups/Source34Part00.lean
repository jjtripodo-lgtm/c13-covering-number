import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source34
namespace C13.Global.FastDual34_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,9]
def points : Finset C13.Point := {1,3,7,9}
def columns : List Code := [381,471,829,885,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1653,1654,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2413,2421,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2876,2901,2932,2986,3011,3042,3127,3187,3189,3190,3277,3292,3308,3351,3379,3381,3382,3405,3411,3413,3414,3417,3418,3420,3429,3433,3436,3441,3442,3444,3448,3477,3478,3493,3508,3525,3532,3540,3556,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 519,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 2337,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 2256,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 1824,1,1⟩,⟨.covers 1728,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source34.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source34.rootCodes link34 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual34_000
namespace C13.Global.FastDual34_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,10]
def points : Finset C13.Point := {1,3,7,10}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1371,1374,1395,1398,1402,1461,1509,1639,1651,1654,1693,1721,1753,1882,1894,1906,1945,1957,1969,2413,2421,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2861,2869,2873,2876,2901,2917,2921,2924,2929,2932,2936,2951,2963,2966,2979,2982,2986,2994,3011,3014,3026,3042,3127,3187,3190,3277,3292,3308,3379,3418,3442,3493,3532,3556,3623,3635,3686,3698,3725,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 75,1,11⟩,⟨.covers 139,1,16⟩,⟨.covers 147,1,2⟩,⟨.covers 99,1,4⟩,⟨.covers 2307,1,2⟩,⟨.covers 269,1,4⟩,⟨.covers 2069,1,2⟩,⟨.covers 581,1,1⟩,⟨.covers 201,1,11⟩,⟨.covers 2121,1,3⟩,⟨.covers 777,1,4⟩,⟨.covers 1289,1,5⟩,⟨.covers 705,1,1⟩,⟨.covers 2369,1,2⟩,⟨.covers 1793,1,4⟩,⟨.covers 3329,1,5⟩,⟨.covers 3585,1,1⟩,⟨.covers 78,1,5⟩,⟨.covers 142,1,9⟩,⟨.covers 582,1,2⟩,⟨.covers 774,1,3⟩,⟨.covers 3078,1,4⟩,⟨.covers 154,1,3⟩,⟨.covers 106,1,5⟩,⟨.covers 202,1,11⟩,⟨.covers 2314,1,11⟩,⟨.covers 1546,1,16⟩,⟨.covers 3082,1,5⟩,⟨.covers 114,1,3⟩,⟨.covers 210,1,4⟩,⟨.covers 2818,1,2⟩,⟨.covers 3586,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 108,1,2⟩,⟨.covers 172,1,7⟩,⟨.covers 1292,1,11⟩,⟨.covers 2316,1,3⟩,⟨.covers 1548,1,12⟩,⟨.covers 180,1,5⟩,⟨.covers 564,1,2⟩,⟨.covers 212,1,1⟩,⟨.covers 2196,1,2⟩,⟨.covers 228,1,5⟩,⟨.covers 120,1,4⟩,⟨.covers 184,1,14⟩,⟨.covers 312,1,4⟩,⟨.covers 2824,1,3⟩,⟨.covers 2352,1,1⟩,⟨.covers 3216,1,9⟩,⟨.covers 3600,1,3⟩,⟨.covers 864,1,2⟩,⟨.covers 1728,1,1⟩,⟨.incident 1,8,-3⟩,⟨.incident 3,8,-9⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source34.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source34.rootCodes link34 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual34_001
namespace C13.Global.FastDual34_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,11]
def points : Finset C13.Point := {1,3,7,11}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1651,1653,1654,1693,1721,1753,1821,1845,1849,1852,1863,1875,1877,1878,1881,1882,1884,1891,1893,1894,1905,1906,1908,1912,1941,1945,1957,1969,1987,1989,2001,2017,2413,2421,2425,2455,2486,2518,2677,2731,2734,2746,2794,2901,2921,2929,2966,2986,2994,3127,3187,3189,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 3456,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source34.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source34.rootCodes link34 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual34_002
namespace C13.Global.FastDual34_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,9,11]
def points : Finset C13.Point := {1,3,9,11}
def columns : List Code := [247,251,253,254,381,471,499,501,502,505,506,508,701,743,755,757,758,761,762,764,829,885,892,953,956,967,979,981,995,998,1009,1010,1012,1016,1143,1245,1267,1269,1270,1273,1274,1276,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1491,1493,1494,1497,1498,1500,1509,1521,1522,1524,1528,1639,1653,1654,1693,1721,1724,1749,1753,1763,1766,1777,1778,1780,1784,1821,1852,1863,1877,1894,1908,1945,1976,1987,2001,2018,2032,2231,2285,2291,2293,2294,2297,2298,2300,2413,2421,2425,2455,2483,2486,2517,2518,2537,2540,2545,2546,2548,2552,2677,2731,2734,2746,2773,2794,2801,2802,2804,2808,2901,2986,3056,3127,3187,3189,3251,3254,3277,3285,3292,3305,3308,3313,3314,3316,3320,3351,3379,3405,3413,3433,3441,3478,3506,3532,3540,3560,3568,3669,3754,3824]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 267,1,2⟩,⟨.covers 523,1,2⟩,⟨.covers 1539,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 1185,1,1⟩,⟨.covers 2817,1,2⟩,⟨.covers 3585,1,2⟩,⟨.covers 270,1,2⟩,⟨.covers 526,1,2⟩,⟨.covers 3078,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 778,1,2⟩,⟨.covers 1546,1,2⟩,⟨.covers 2316,1,1⟩,⟨.covers 420,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 1824,1,1⟩,⟨.covers 2752,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source34.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source34.rootCodes link34 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual34_003
namespace C13.Global.FastDual34_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,9,10]
def points : Finset C13.Point := {1,7,9,10}
def columns : List Code := [381,471,637,747,829,861,885,892,967,971,979,995,1143,1147,1150,1213,1245,1261,1371,1374,1395,1398,1402,1437,1453,1461,1485,1509,1639,1646,1654,1693,1721,1753,1894,1945,2173,2238,2365,2397,2413,2421,2425,2428,2455,2462,2486,2518,2621,2653,2677,2684,2731,2734,2746,2794,2845,2876,2901,2932,2955,2986,3011,3042,3127,3131,3187,3190,3194,3229,3245,3277,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 519,1,6⟩,⟨.covers 2055,1,5⟩,⟨.covers 75,1,1⟩,⟨.covers 1035,1,4⟩,⟨.covers 83,1,1⟩,⟨.covers 2563,1,13⟩,⟨.covers 141,1,1⟩,⟨.covers 525,1,4⟩,⟨.covers 197,1,2⟩,⟨.covers 773,1,4⟩,⟨.covers 1541,1,10⟩,⟨.covers 3077,1,3⟩,⟨.covers 2129,1,4⟩,⟨.covers 1313,1,1⟩,⟨.covers 3105,1,1⟩,⟨.covers 1793,1,8⟩,⟨.covers 3585,1,15⟩,⟨.covers 270,1,5⟩,⟨.covers 166,1,5⟩,⟨.covers 2566,1,4⟩,⟨.covers 202,1,12⟩,⟨.covers 1546,1,16⟩,⟨.covers 3082,1,3⟩,⟨.covers 210,1,1⟩,⟨.covers 1794,1,16⟩,⟨.covers 3586,1,12⟩,⟨.covers 300,1,4⟩,⟨.covers 1292,1,1⟩,⟨.covers 2572,1,4⟩,⟨.covers 228,1,4⟩,⟨.covers 2248,1,1⟩,⟨.covers 1352,1,2⟩,⟨.covers 3336,1,1⟩,⟨.covers 624,1,4⟩,⟨.covers 688,1,9⟩,⟨.covers 1328,1,6⟩,⟨.covers 2608,1,4⟩,⟨.covers 2256,1,4⟩,⟨.covers 848,1,4⟩,⟨.covers 1616,1,12⟩,⟨.covers 3152,1,2⟩,⟨.covers 912,1,6⟩,⟨.covers 928,1,13⟩,⟨.covers 1696,1,6⟩,⟨.covers 3232,1,2⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,3⟩,⟨.covers 3456,1,1⟩,⟨.incident 1,8,-1⟩,⟨.incident 9,8,-8⟩,⟨.incident 10,8,-3⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source34.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source34.rootCodes link34 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual34_004
namespace C13.Global.FastDual34_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,9,11]
def points : Finset C13.Point := {1,7,9,11}
def columns : List Code := [381,471,637,747,829,861,885,892,967,971,979,995,1143,1147,1149,1150,1213,1245,1261,1341,1367,1371,1373,1374,1389,1395,1397,1398,1401,1402,1404,1437,1453,1461,1485,1493,1509,1597,1629,1639,1646,1653,1654,1660,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2173,2238,2397,2413,2421,2425,2455,2462,2486,2518,2653,2677,2731,2734,2746,2794,2901,2986,3127,3131,3165,3181,3187,3189,3193,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 2055,1,11⟩,⟨.covers 267,1,11⟩,⟨.covers 99,1,5⟩,⟨.covers 1539,1,5⟩,⟨.covers 2563,1,11⟩,⟨.covers 525,1,5⟩,⟨.covers 2061,1,5⟩,⟨.covers 297,1,3⟩,⟨.covers 3081,1,5⟩,⟨.covers 2817,1,11⟩,⟨.covers 3585,1,11⟩,⟨.covers 78,1,5⟩,⟨.covers 142,1,3⟩,⟨.covers 270,1,5⟩,⟨.covers 198,1,11⟩,⟨.covers 2566,1,8⟩,⟨.covers 154,1,3⟩,⟨.covers 114,1,5⟩,⟨.covers 226,1,3⟩,⟨.covers 1794,1,5⟩,⟨.covers 2818,1,11⟩,⟨.covers 3586,1,11⟩,⟨.covers 300,1,3⟩,⟨.covers 1548,1,5⟩,⟨.covers 180,1,3⟩,⟨.covers 228,1,11⟩,⟨.covers 216,1,11⟩,⟨.covers 624,1,5⟩,⟨.covers 688,1,3⟩,⟨.covers 1200,1,8⟩,⟨.covers 2352,1,8⟩,⟨.covers 2608,1,5⟩,⟨.covers 912,1,11⟩,⟨.covers 864,1,3⟩,⟨.covers 1824,1,3⟩,⟨.covers 3360,1,3⟩,⟨.covers 2752,1,8⟩,⟨.covers 3456,1,11⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source34.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source34.rootCodes link34 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual34_005
namespace C13.Global.FastDual34_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,10,11]
def points : Finset C13.Point := {1,7,10,11}
def columns : List Code := [381,471,637,747,829,861,877,885,889,892,967,971,979,995,1143,1147,1150,1213,1245,1261,1371,1374,1395,1398,1402,1437,1453,1461,1485,1509,1639,1646,1651,1654,1658,1693,1709,1721,1741,1753,1870,1882,1894,1906,1933,1945,1957,1969,2173,2238,2397,2413,2421,2425,2455,2462,2486,2518,2653,2669,2677,2681,2731,2734,2746,2794,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3187,3277,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 519,1,5⟩,⟨.covers 267,1,6⟩,⟨.covers 2059,1,8⟩,⟨.covers 2307,1,5⟩,⟨.covers 141,1,3⟩,⟨.covers 2061,1,4⟩,⟨.covers 149,1,2⟩,⟨.covers 533,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,2⟩,⟨.covers 297,1,3⟩,⟨.covers 1289,1,2⟩,⟨.covers 2569,1,4⟩,⟨.covers 1793,1,1⟩,⟨.covers 3329,1,10⟩,⟨.covers 3585,1,15⟩,⟨.covers 78,1,6⟩,⟨.covers 86,1,2⟩,⟨.covers 166,1,8⟩,⟨.covers 550,1,2⟩,⟨.covers 2566,1,1⟩,⟨.covers 3078,1,15⟩,⟨.covers 282,1,1⟩,⟨.covers 2314,1,10⟩,⟨.covers 1546,1,2⟩,⟨.covers 3082,1,7⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,6⟩,⟨.covers 180,1,2⟩,⟨.covers 564,1,1⟩,⟨.covers 596,1,3⟩,⟨.covers 420,1,1⟩,⟨.covers 804,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 792,1,1⟩,⟨.covers 1560,1,2⟩,⟨.covers 1800,1,2⟩,⟨.covers 3336,1,10⟩,⟨.covers 3592,1,15⟩,⟨.covers 2160,1,3⟩,⟨.covers 1200,1,2⟩,⟨.covers 720,1,5⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,2⟩,⟨.covers 3152,1,12⟩,⟨.covers 1424,1,3⟩,⟨.covers 2704,1,10⟩,⟨.covers 3216,1,3⟩,⟨.covers 2272,1,2⟩,⟨.covers 1376,1,7⟩,⟨.covers 2656,1,3⟩,⟨.covers 1696,1,5⟩,⟨.covers 3232,1,13⟩,⟨.covers 2848,1,1⟩,⟨.covers 2496,1,4⟩,⟨.incident 10,8,-4⟩,⟨.incident 11,8,-5⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source34.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source34.rootCodes link34 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual34_006
namespace C13.Global.FastDual34_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,10]
def points : Finset C13.Point := {3,7,9,10}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1371,1374,1383,1395,1398,1402,1447,1461,1509,1639,1654,1691,1693,1721,1753,1894,1945,2167,2286,2359,2391,2407,2411,2413,2414,2419,2421,2422,2425,2426,2428,2455,2471,2486,2503,2518,2534,2647,2663,2677,2678,2731,2734,2746,2794,2862,2876,2887,2901,2918,2932,2986,3011,3042,3127,3175,3187,3190,3277,3278,3292,3308,3367,3379,3406,3418,3430,3442,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 519,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 1793,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 2224,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source34.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source34.rootCodes link34 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual34_007
