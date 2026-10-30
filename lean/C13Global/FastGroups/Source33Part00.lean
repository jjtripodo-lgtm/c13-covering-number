import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source33
namespace C13.Global.FastDual33_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,9]
def points : Finset C13.Point := {1,3,6,9}
def columns : List Code := [701,743,829,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2231,2285,2413,2425,2455,2483,2485,2486,2537,2677,2731,2734,2745,2746,2748,2773,2876,2901,2986,3000,3011,3025,3127,3251,3253,3254,3277,3292,3308,3351,3379,3381,3382,3405,3417,3418,3420,3433,3436,3448,3475,3477,3478,3493,3505,3506,3508,3529,3532,3544,3560,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 2055,1,4⟩,⟨.covers 75,1,4⟩,⟨.covers 139,1,15⟩,⟨.covers 83,1,7⟩,⟨.covers 147,1,4⟩,⟨.covers 99,1,1⟩,⟨.covers 1539,1,9⟩,⟨.covers 141,1,2⟩,⟨.covers 1157,1,3⟩,⟨.covers 89,1,4⟩,⟨.covers 297,1,3⟩,⟨.covers 201,1,1⟩,⟨.covers 777,1,3⟩,⟨.covers 3081,1,4⟩,⟨.covers 1073,1,3⟩,⟨.covers 2817,1,7⟩,⟨.covers 3585,1,7⟩,⟨.covers 78,1,15⟩,⟨.covers 142,1,15⟩,⟨.covers 198,1,8⟩,⟨.covers 390,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 3078,1,4⟩,⟨.covers 106,1,14⟩,⟨.covers 202,1,15⟩,⟨.covers 778,1,3⟩,⟨.covers 2314,1,8⟩,⟨.covers 1546,1,15⟩,⟨.covers 178,1,4⟩,⟨.covers 2818,1,4⟩,⟨.covers 3330,1,4⟩,⟨.covers 156,1,3⟩,⟨.covers 300,1,4⟩,⟨.covers 1164,1,2⟩,⟨.covers 2316,1,4⟩,⟨.covers 1548,1,1⟩,⟨.covers 212,1,7⟩,⟨.covers 228,1,1⟩,⟨.covers 1188,1,1⟩,⟨.covers 2436,1,2⟩,⟨.covers 120,1,1⟩,⟨.covers 184,1,5⟩,⟨.covers 232,1,7⟩,⟨.covers 1800,1,6⟩,⟨.covers 3336,1,4⟩,⟨.covers 2352,1,4⟩,⟨.covers 864,1,9⟩,⟨.covers 2656,1,7⟩,⟨.covers 1920,1,1⟩,⟨.incident 1,8,-4⟩,⟨.incident 3,8,-4⟩]
def bound : Int := 8

theorem column_mask : listMask columns = restrictMask universeMask Source33.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source33.rootCodes link33 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual33_000
namespace C13.Global.FastDual33_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,10]
def points : Finset C13.Point := {1,3,6,10}
def columns : List Code := [701,743,829,949,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1766,1882,1894,1906,1945,1957,1969,2231,2285,2413,2425,2455,2483,2485,2486,2537,2677,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2773,2789,2861,2869,2873,2876,2901,2917,2921,2929,2951,2963,2965,2966,2979,2981,2982,2985,2986,2988,2993,2994,2996,3000,3011,3013,3025,3041,3127,3251,3253,3277,3292,3308,3379,3418,3493,3505,3532,3544,3623,3635,3686,3725,3737,3749,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 139,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 1793,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 2880,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source33.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source33.rootCodes link33 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual33_001
namespace C13.Global.FastDual33_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,11]
def points : Finset C13.Point := {1,3,6,11}
def columns : List Code := [701,743,829,949,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1724,1766,1821,1845,1849,1852,1863,1875,1878,1882,1891,1894,1906,1941,1945,1948,1957,1969,1972,1976,1987,1990,2002,2018,2231,2285,2413,2425,2455,2483,2486,2537,2677,2731,2734,2739,2742,2746,2773,2901,2921,2929,2966,2986,2994,3127,3251,3254,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796,3851,3859,3913,3921,3978,3986,4040,4048]
def rows : List LinearRow := [⟨.covers 139,1,2⟩,⟨.covers 525,1,1⟩,⟨.covers 89,1,2⟩,⟨.covers 201,1,2⟩,⟨.covers 78,1,2⟩,⟨.covers 142,1,2⟩,⟨.covers 154,1,1⟩,⟨.covers 106,1,2⟩,⟨.covers 202,1,1⟩,⟨.covers 1546,1,2⟩,⟨.covers 2316,1,2⟩,⟨.covers 1548,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 808,1,1⟩,⟨.covers 3168,1,2⟩,⟨.incident 3,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source33.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source33.rootCodes link33 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual33_002
namespace C13.Global.FastDual33_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,9]
def points : Finset C13.Point := {1,3,7,9}
def columns : List Code := [381,471,829,885,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1653,1654,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2413,2421,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2876,2901,2932,2986,3011,3042,3127,3187,3189,3190,3277,3292,3308,3351,3379,3381,3382,3405,3411,3413,3414,3417,3418,3420,3429,3433,3436,3441,3442,3444,3448,3477,3478,3493,3508,3525,3532,3540,3556,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 519,1,1⟩,⟨.covers 75,1,11⟩,⟨.covers 139,1,11⟩,⟨.covers 147,1,11⟩,⟨.covers 99,1,7⟩,⟨.covers 1059,1,3⟩,⟨.covers 141,1,11⟩,⟨.covers 777,1,9⟩,⟨.covers 2337,1,6⟩,⟨.covers 2817,1,5⟩,⟨.covers 3585,1,11⟩,⟨.covers 78,1,11⟩,⟨.covers 142,1,11⟩,⟨.covers 774,1,10⟩,⟨.covers 3078,1,8⟩,⟨.covers 154,1,11⟩,⟨.covers 202,1,2⟩,⟨.covers 778,1,11⟩,⟨.covers 1546,1,6⟩,⟨.covers 3082,1,3⟩,⟨.covers 114,1,1⟩,⟨.covers 226,1,3⟩,⟨.covers 3330,1,3⟩,⟨.covers 3586,1,2⟩,⟨.covers 300,1,2⟩,⟨.covers 2316,1,4⟩,⟨.covers 180,1,7⟩,⟨.covers 228,1,11⟩,⟨.covers 120,1,6⟩,⟨.covers 1800,1,2⟩,⟨.covers 3336,1,6⟩,⟨.covers 624,1,3⟩,⟨.covers 1200,1,4⟩,⟨.covers 1584,1,7⟩,⟨.covers 2256,1,11⟩,⟨.covers 2832,1,6⟩,⟨.covers 864,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 1728,1,11⟩,⟨.covers 2752,1,6⟩,⟨.covers 2880,1,1⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source33.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source33.rootCodes link33 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual33_003
namespace C13.Global.FastDual33_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,10]
def points : Finset C13.Point := {1,3,7,10}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1371,1374,1395,1398,1402,1461,1509,1639,1651,1654,1693,1721,1753,1882,1894,1906,1945,1957,1969,2413,2421,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2861,2869,2873,2876,2901,2917,2921,2924,2929,2932,2936,2951,2963,2966,2979,2982,2986,2994,3011,3014,3026,3042,3127,3187,3190,3277,3292,3308,3379,3418,3442,3493,3532,3556,3623,3635,3686,3698,3725,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 2055,1,2⟩,⟨.covers 75,1,14⟩,⟨.covers 139,1,13⟩,⟨.covers 147,1,6⟩,⟨.covers 99,1,6⟩,⟨.covers 2307,1,1⟩,⟨.covers 1539,1,1⟩,⟨.covers 269,1,4⟩,⟨.covers 2069,1,3⟩,⟨.covers 537,1,1⟩,⟨.covers 201,1,6⟩,⟨.covers 2121,1,1⟩,⟨.covers 777,1,3⟩,⟨.covers 3081,1,4⟩,⟨.covers 2129,1,1⟩,⟨.covers 705,1,4⟩,⟨.covers 2369,1,2⟩,⟨.covers 2625,1,2⟩,⟨.covers 1793,1,7⟩,⟨.covers 3329,1,9⟩,⟨.covers 3585,1,1⟩,⟨.covers 78,1,5⟩,⟨.covers 142,1,13⟩,⟨.covers 2070,1,1⟩,⟨.covers 198,1,2⟩,⟨.covers 774,1,6⟩,⟨.covers 3078,1,6⟩,⟨.covers 154,1,6⟩,⟨.covers 106,1,3⟩,⟨.covers 202,1,10⟩,⟨.covers 2314,1,7⟩,⟨.covers 1546,1,13⟩,⟨.covers 3082,1,6⟩,⟨.covers 114,1,5⟩,⟨.covers 210,1,2⟩,⟨.covers 2818,1,4⟩,⟨.covers 3586,1,2⟩,⟨.covers 156,1,3⟩,⟨.covers 108,1,2⟩,⟨.covers 1292,1,9⟩,⟨.covers 2316,1,2⟩,⟨.covers 1548,1,6⟩,⟨.covers 180,1,9⟩,⟨.covers 564,1,2⟩,⟨.covers 212,1,1⟩,⟨.covers 2580,1,1⟩,⟨.covers 228,1,9⟩,⟨.covers 1604,1,4⟩,⟨.covers 120,1,5⟩,⟨.covers 184,1,8⟩,⟨.covers 2824,1,1⟩,⟨.covers 2352,1,2⟩,⟨.covers 2256,1,5⟩,⟨.covers 2832,1,1⟩,⟨.covers 3600,1,5⟩,⟨.covers 864,1,2⟩,⟨.covers 928,1,1⟩,⟨.covers 1696,1,2⟩,⟨.incident 1,8,-3⟩,⟨.incident 3,8,-1⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source33.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source33.rootCodes link33 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual33_004
namespace C13.Global.FastDual33_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,11]
def points : Finset C13.Point := {1,3,7,11}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1651,1653,1654,1693,1721,1753,1821,1845,1849,1852,1863,1875,1877,1878,1881,1882,1884,1891,1893,1894,1905,1906,1908,1912,1941,1945,1957,1969,1987,1989,2001,2017,2413,2421,2425,2455,2486,2518,2677,2731,2734,2746,2794,2901,2921,2929,2966,2986,2994,3127,3187,3189,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816,3851,3859,3913,3921,3978,3986,4040,4048]
def rows : List LinearRow := [⟨.covers 75,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 2464,1,1⟩,⟨.incident 1,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source33.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source33.rootCodes link33 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual33_005
namespace C13.Global.FastDual33_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,9,11]
def points : Finset C13.Point := {1,3,9,11}
def columns : List Code := [247,251,253,254,381,471,499,501,502,505,506,508,701,743,755,757,758,761,762,764,829,885,892,953,956,967,979,981,995,998,1009,1010,1012,1016,1143,1245,1267,1269,1270,1273,1274,1276,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1491,1493,1494,1497,1498,1500,1509,1521,1522,1524,1528,1639,1653,1654,1693,1721,1724,1749,1753,1763,1766,1777,1778,1780,1784,1821,1852,1863,1877,1894,1908,1945,1976,1987,2001,2018,2032,2231,2285,2291,2293,2294,2297,2298,2300,2413,2421,2425,2455,2483,2486,2517,2518,2537,2540,2545,2546,2548,2552,2677,2731,2734,2746,2773,2794,2801,2802,2804,2808,2901,2986,3056,3127,3187,3189,3251,3254,3277,3285,3292,3305,3308,3313,3314,3316,3320,3351,3379,3405,3413,3433,3441,3478,3506,3532,3540,3560,3568,3669,3754,3824]
def rows : List LinearRow := [⟨.covers 135,1,8⟩,⟨.covers 519,1,3⟩,⟨.covers 2055,1,2⟩,⟨.covers 267,1,20⟩,⟨.covers 523,1,21⟩,⟨.covers 147,1,2⟩,⟨.covers 2307,1,5⟩,⟨.covers 1539,1,6⟩,⟨.covers 141,1,9⟩,⟨.covers 525,1,2⟩,⟨.covers 2061,1,3⟩,⟨.covers 201,1,5⟩,⟨.covers 777,1,10⟩,⟨.covers 3081,1,4⟩,⟨.covers 2097,1,2⟩,⟨.covers 657,1,2⟩,⟨.covers 2145,1,3⟩,⟨.covers 1185,1,7⟩,⟨.covers 2817,1,18⟩,⟨.covers 3585,1,18⟩,⟨.covers 270,1,20⟩,⟨.covers 526,1,21⟩,⟨.covers 198,1,1⟩,⟨.covers 774,1,3⟩,⟨.covers 3078,1,9⟩,⟨.covers 154,1,13⟩,⟨.covers 778,1,21⟩,⟨.covers 1546,1,21⟩,⟨.covers 1074,1,1⟩,⟨.covers 2098,1,2⟩,⟨.covers 1122,1,4⟩,⟨.covers 1794,1,4⟩,⟨.covers 3330,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 2316,1,8⟩,⟨.covers 1548,1,7⟩,⟨.covers 212,1,4⟩,⟨.covers 612,1,3⟩,⟨.covers 420,1,7⟩,⟨.covers 1188,1,3⟩,⟨.covers 312,1,1⟩,⟨.covers 568,1,7⟩,⟨.covers 360,1,6⟩,⟨.covers 3336,1,6⟩,⟨.covers 1136,1,2⟩,⟨.covers 2352,1,6⟩,⟨.covers 1584,1,4⟩,⟨.covers 1808,1,2⟩,⟨.covers 864,1,2⟩,⟨.covers 3168,1,2⟩,⟨.covers 2752,1,10⟩,⟨.covers 1920,1,7⟩,⟨.covers 3456,1,7⟩,⟨.incident 3,8,-4⟩,⟨.incident 11,8,-1⟩]
def bound : Int := 18

theorem column_mask : listMask columns = restrictMask universeMask Source33.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source33.rootCodes link33 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual33_006
namespace C13.Global.FastDual33_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,9]
def points : Finset C13.Point := {1,6,7,9}
def columns : List Code := [829,967,971,979,995,1150,1213,1341,1371,1374,1402,1437,1453,1461,1597,1639,1646,1654,1693,1721,1821,1852,1863,1894,1945,1987,2173,2238,2365,2397,2413,2425,2455,2462,2486,2621,2653,2677,2731,2734,2746,2845,2876,2901,2955,2986,3011,3127,3131,3133,3134,3165,3181,3196,3229,3245,3260,3277,3292,3308,3351,3355,3357,3358,3373,3379,3381,3382,3385,3386,3388,3405,3417,3418,3420,3433,3436,3448,3469,3477,3478,3484,3493,3500,3508,3532,3613,3630,3644,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 2055,1,8⟩,⟨.covers 75,1,8⟩,⟨.covers 139,1,2⟩,⟨.covers 2059,1,8⟩,⟨.covers 1059,1,4⟩,⟨.covers 1539,1,6⟩,⟨.covers 77,1,6⟩,⟨.covers 141,1,6⟩,⟨.covers 525,1,2⟩,⟨.covers 149,1,4⟩,⟨.covers 101,1,2⟩,⟨.covers 293,1,2⟩,⟨.covers 89,1,4⟩,⟨.covers 169,1,2⟩,⟨.covers 297,1,2⟩,⟨.covers 3585,1,9⟩,⟨.covers 78,1,4⟩,⟨.covers 142,1,4⟩,⟨.covers 270,1,8⟩,⟨.covers 166,1,8⟩,⟨.covers 198,1,11⟩,⟨.covers 106,1,8⟩,⟨.covers 778,1,2⟩,⟨.covers 210,1,11⟩,⟨.covers 226,1,8⟩,⟨.covers 1794,1,6⟩,⟨.covers 3330,1,4⟩,⟨.covers 3586,1,11⟩,⟨.covers 212,1,11⟩,⟨.covers 228,1,11⟩,⟨.covers 808,1,2⟩,⟨.covers 1800,1,9⟩,⟨.covers 624,1,9⟩,⟨.covers 688,1,9⟩,⟨.covers 2384,1,2⟩,⟨.covers 1616,1,2⟩,⟨.covers 1424,1,2⟩,⟨.covers 2704,1,2⟩,⟨.covers 2832,1,9⟩,⟨.covers 1376,1,4⟩,⟨.covers 928,1,4⟩,⟨.covers 2464,1,4⟩,⟨.covers 2752,1,11⟩,⟨.covers 3392,1,6⟩,⟨.covers 3456,1,6⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source33.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source33.rootCodes link33 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual33_007
