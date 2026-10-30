import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source28
namespace C13.Global.FastDual28_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,3,10]
def points : Finset C13.Point := {1,2,3,10}
def columns : List Code := [247,251,253,254,499,501,502,505,506,508,755,757,758,761,762,764,829,885,889,892,949,953,956,979,995,1009,1010,1012,1016,1267,1269,1270,1273,1274,1276,1371,1395,1402,1461,1497,1498,1509,1521,1522,1524,1528,1639,1651,1654,1721,1753,1765,1766,1777,1778,1780,1784,1882,1894,1906,1945,1957,1969,2008,2020,2032,2291,2293,2294,2297,2298,2300,2425,2455,2483,2485,2486,2515,2517,2518,2537,2545,2546,2548,2552,2677,2731,2739,2745,2746,2773,2787,2793,2794,2801,2802,2804,2808,2869,2873,2876,2901,2921,2929,2932,2936,2963,2965,2966,2979,2985,2986,2993,2994,2996,3000,3011,3025,3026,3028,3041,3042,3048,3056,3187,3251,3277,3289,3292,3301,3308,3313,3314,3316,3320,3379,3418,3442,3493,3505,3532,3544,3556,3568,3635,3686,3698,3737,3761,3788,3800,3812,3824,3854,3866,3878,3890,3980,3992,4004,4016]
def rows : List LinearRow := [⟨.covers 263,1,4⟩,⟨.covers 519,1,3⟩,⟨.covers 75,1,3⟩,⟨.covers 139,1,1⟩,⟨.covers 523,1,3⟩,⟨.covers 77,1,3⟩,⟨.covers 269,1,4⟩,⟨.covers 1553,1,1⟩,⟨.covers 3089,1,1⟩,⟨.covers 1313,1,1⟩,⟨.covers 3105,1,1⟩,⟨.covers 1409,1,1⟩,⟨.covers 1665,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 2098,1,1⟩,⟨.covers 450,1,2⟩,⟨.covers 706,1,2⟩,⟨.covers 834,1,1⟩,⟨.covers 898,1,2⟩,⟨.covers 596,1,2⟩,⟨.covers 2132,1,2⟩,⟨.covers 2580,1,2⟩,⟨.covers 420,1,1⟩,⟨.covers 2628,1,1⟩,⟨.covers 664,1,1⟩,⟨.covers 360,1,2⟩,⟨.covers 2152,1,2⟩,⟨.covers 2344,1,2⟩,⟨.covers 2376,1,1⟩,⟨.covers 1200,1,2⟩,⟨.covers 1616,1,1⟩,⟨.covers 3152,1,1⟩,⟨.covers 1808,1,1⟩,⟨.covers 3344,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 1824,1,1⟩,⟨.covers 3616,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 3456,1,1⟩,⟨.covers 3712,1,1⟩,⟨.incident 1,8,3⟩,⟨.incident 2,8,3⟩,⟨.incident 3,8,3⟩,⟨.incident 10,8,1⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_000
namespace C13.Global.FastDual28_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,7,9]
def points : Finset C13.Point := {1,2,7,9}
def columns : List Code := [637,747,829,885,892,971,979,995,1147,1261,1371,1395,1401,1402,1453,1461,1509,1639,1646,1653,1654,1660,1721,1753,1852,1894,1908,1945,1987,2001,2425,2455,2462,2486,2518,2653,2677,2684,2731,2746,2794,2845,2876,2901,2932,2955,2986,3011,3042,3131,3187,3193,3194,3277,3292,3308,3355,3379,3385,3386,3411,3417,3418,3433,3441,3442,3448,3469,3477,3478,3484,3493,3500,3508,3525,3532,3540,3556,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,2⟩,⟨.covers 83,1,1⟩,⟨.covers 1539,1,2⟩,⟨.covers 2563,1,2⟩,⟨.covers 78,1,2⟩,⟨.covers 142,1,2⟩,⟨.covers 86,1,1⟩,⟨.covers 774,1,2⟩,⟨.covers 2566,1,1⟩,⟨.covers 202,1,2⟩,⟨.covers 3082,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 178,1,2⟩,⟨.covers 210,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 928,1,2⟩,⟨.incident 1,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_001
namespace C13.Global.FastDual28_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,7,10]
def points : Finset C13.Point := {1,2,7,10}
def columns : List Code := [637,747,829,885,889,892,971,979,995,1147,1261,1371,1395,1402,1453,1461,1509,1639,1646,1651,1654,1658,1721,1753,1882,1894,1906,1945,1957,1969,2425,2455,2462,2486,2518,2653,2677,2681,2684,2731,2746,2794,2845,2869,2873,2876,2901,2905,2908,2921,2929,2932,2936,2955,2963,2966,2970,2979,2986,2994,3011,3018,3026,3042,3131,3187,3194,3277,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3635,3686,3698,3737,3788,3800,3854,3866,3878,3890,3980,3992,4004,4016]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 149,1,2⟩,⟨.covers 773,1,1⟩,⟨.covers 1541,1,1⟩,⟨.covers 3077,1,2⟩,⟨.covers 78,1,2⟩,⟨.covers 86,1,1⟩,⟨.covers 166,1,2⟩,⟨.covers 198,1,1⟩,⟨.covers 774,1,2⟩,⟨.covers 156,1,2⟩,⟨.covers 172,1,2⟩,⟨.covers 116,1,1⟩,⟨.covers 2628,1,1⟩,⟨.covers 1472,1,2⟩,⟨.incident 2,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_002
namespace C13.Global.FastDual28_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,7,11]
def points : Finset C13.Point := {1,2,7,11}
def columns : List Code := [637,747,829,885,889,892,971,979,995,1147,1261,1371,1395,1401,1402,1453,1461,1509,1639,1643,1645,1646,1651,1653,1654,1657,1658,1660,1721,1753,1769,1837,1845,1849,1852,1867,1875,1881,1882,1891,1893,1894,1897,1898,1900,1905,1906,1908,1912,1945,1957,1961,1969,1987,1993,2001,2017,2425,2455,2462,2486,2518,2653,2677,2681,2731,2746,2794,2901,2921,2929,2966,2986,2994,3131,3187,3193,3277,3292,3308,3379,3433,3441,3478,3532,3540,3627,3635,3661,3669,3689,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 71,1,12⟩,⟨.covers 139,1,2⟩,⟨.covers 267,1,9⟩,⟨.covers 83,1,1⟩,⟨.covers 1043,1,2⟩,⟨.covers 163,1,8⟩,⟨.covers 2307,1,2⟩,⟨.covers 269,1,5⟩,⟨.covers 2061,1,9⟩,⟨.covers 149,1,8⟩,⟨.covers 533,1,2⟩,⟨.covers 773,1,1⟩,⟨.covers 2309,1,2⟩,⟨.covers 3077,1,2⟩,⟨.covers 78,1,12⟩,⟨.covers 142,1,12⟩,⟨.covers 166,1,12⟩,⟨.covers 198,1,12⟩,⟨.covers 2566,1,12⟩,⟨.covers 3078,1,12⟩,⟨.covers 778,1,1⟩,⟨.covers 3082,1,10⟩,⟨.covers 114,1,6⟩,⟨.covers 226,1,1⟩,⟨.covers 1794,1,2⟩,⟨.covers 3586,1,2⟩,⟨.covers 172,1,3⟩,⟨.covers 1292,1,2⟩,⟨.covers 116,1,5⟩,⟨.covers 228,1,7⟩,⟨.covers 1796,1,2⟩,⟨.covers 120,1,3⟩,⟨.covers 184,1,10⟩,⟨.covers 216,1,10⟩,⟨.covers 792,1,3⟩,⟨.covers 2824,1,3⟩,⟨.covers 3336,1,5⟩,⟨.covers 2160,1,2⟩,⟨.covers 1328,1,3⟩,⟨.covers 2608,1,1⟩,⟨.covers 1808,1,1⟩,⟨.covers 3600,1,7⟩,⟨.covers 928,1,1⟩,⟨.covers 2848,1,7⟩,⟨.covers 3360,1,6⟩,⟨.covers 1472,1,3⟩,⟨.covers 2752,1,10⟩,⟨.covers 1920,1,6⟩,⟨.incident 1,8,-1⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_003
namespace C13.Global.FastDual28_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,9,10]
def points : Finset C13.Point := {1,2,9,10}
def columns : List Code := [247,251,253,254,445,475,499,501,502,505,506,508,637,747,755,757,758,761,762,764,829,885,892,953,956,971,979,985,995,1002,1009,1010,1012,1016,1147,1261,1267,1269,1270,1273,1274,1276,1371,1395,1402,1453,1461,1465,1497,1498,1509,1516,1521,1522,1524,1528,1639,1646,1654,1721,1753,1766,1777,1778,1780,1784,1894,1945,2032,2235,2269,2291,2293,2294,2297,2298,2300,2425,2455,2459,2461,2462,2483,2485,2486,2489,2490,2492,2515,2517,2518,2521,2522,2524,2537,2545,2546,2548,2552,2653,2677,2684,2731,2745,2746,2773,2777,2787,2794,2801,2802,2804,2808,2845,2876,2901,2932,2955,2969,2986,3000,3011,3025,3042,3056,3131,3187,3194,3251,3257,3277,3289,3292,3301,3308,3313,3314,3316,3320,3355,3379,3418,3442,3469,3481,3493,3505,3532,3544,3556,3568,3686,3737,3824]
def rows : List LinearRow := [⟨.covers 263,1,19⟩,⟨.covers 519,1,19⟩,⟨.covers 75,1,8⟩,⟨.covers 523,1,4⟩,⟨.covers 1035,1,3⟩,⟨.covers 83,1,4⟩,⟨.covers 163,1,2⟩,⟨.covers 1283,1,1⟩,⟨.covers 2563,1,7⟩,⟨.covers 77,1,6⟩,⟨.covers 525,1,4⟩,⟨.covers 1037,1,6⟩,⟨.covers 197,1,2⟩,⟨.covers 773,1,11⟩,⟨.covers 3077,1,1⟩,⟨.covers 1073,1,2⟩,⟨.covers 593,1,2⟩,⟨.covers 2145,1,9⟩,⟨.covers 1185,1,4⟩,⟨.covers 270,1,19⟩,⟨.covers 526,1,19⟩,⟨.covers 166,1,11⟩,⟨.covers 774,1,19⟩,⟨.covers 2566,1,19⟩,⟨.covers 2090,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 3082,1,12⟩,⟨.covers 1074,1,1⟩,⟨.covers 338,1,1⟩,⟨.covers 1106,1,1⟩,⟨.covers 674,1,1⟩,⟨.covers 450,1,5⟩,⟨.covers 2818,1,7⟩,⟨.covers 3330,1,3⟩,⟨.covers 92,1,3⟩,⟨.covers 172,1,1⟩,⟨.covers 1292,1,7⟩,⟨.covers 2572,1,2⟩,⟨.covers 308,1,2⟩,⟨.covers 564,1,2⟩,⟨.covers 596,1,1⟩,⟨.covers 2132,1,1⟩,⟨.covers 2244,1,3⟩,⟨.covers 2820,1,2⟩,⟨.covers 3332,1,5⟩,⟨.covers 184,1,4⟩,⟨.covers 568,1,1⟩,⟨.covers 360,1,9⟩,⟨.covers 2152,1,2⟩,⟨.covers 680,1,3⟩,⟨.covers 3144,1,1⟩,⟨.covers 1800,1,19⟩,⟨.covers 3592,1,19⟩,⟨.covers 1328,1,5⟩,⟨.covers 2608,1,4⟩,⟨.covers 2256,1,4⟩,⟨.covers 848,1,2⟩,⟨.covers 1616,1,11⟩,⟨.covers 928,1,1⟩,⟨.covers 2848,1,6⟩,⟨.covers 3360,1,8⟩,⟨.covers 1472,1,2⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_004
namespace C13.Global.FastDual28_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,9]
def points : Finset C13.Point := {1,3,7,9}
def columns : List Code := [381,471,829,885,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1653,1654,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2413,2421,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2876,2901,2932,2986,3011,3042,3127,3187,3189,3190,3277,3292,3308,3351,3379,3381,3382,3405,3411,3413,3414,3417,3418,3420,3429,3433,3436,3441,3442,3444,3448,3477,3478,3493,3508,3525,3532,3540,3556,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 519,1,8⟩,⟨.covers 2055,1,2⟩,⟨.covers 75,1,12⟩,⟨.covers 147,1,8⟩,⟨.covers 163,1,10⟩,⟨.covers 1539,1,2⟩,⟨.covers 525,1,5⟩,⟨.covers 2061,1,3⟩,⟨.covers 169,1,2⟩,⟨.covers 297,1,1⟩,⟨.covers 201,1,7⟩,⟨.covers 1161,1,1⟩,⟨.covers 777,1,5⟩,⟨.covers 3081,1,1⟩,⟨.covers 2097,1,3⟩,⟨.covers 1185,1,2⟩,⟨.covers 2337,1,2⟩,⟨.covers 3105,1,1⟩,⟨.covers 78,1,12⟩,⟨.covers 142,1,12⟩,⟨.covers 198,1,2⟩,⟨.covers 3078,1,4⟩,⟨.covers 154,1,2⟩,⟨.covers 202,1,12⟩,⟨.covers 2314,1,2⟩,⟨.covers 1546,1,12⟩,⟨.covers 114,1,6⟩,⟨.covers 178,1,2⟩,⟨.covers 2818,1,10⟩,⟨.covers 3330,1,4⟩,⟨.covers 156,1,4⟩,⟨.covers 108,1,4⟩,⟨.covers 2316,1,2⟩,⟨.covers 1548,1,2⟩,⟨.covers 180,1,8⟩,⟨.covers 228,1,8⟩,⟨.covers 2820,1,10⟩,⟨.covers 3588,1,6⟩,⟨.covers 120,1,6⟩,⟨.covers 184,1,7⟩,⟨.covers 3336,1,6⟩,⟨.covers 720,1,2⟩,⟨.covers 2256,1,8⟩,⟨.covers 2704,1,1⟩,⟨.covers 3600,1,4⟩,⟨.covers 1824,1,10⟩,⟨.covers 1728,1,2⟩,⟨.covers 1920,1,6⟩,⟨.covers 3456,1,2⟩,⟨.incident 3,8,-2⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_005
namespace C13.Global.FastDual28_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,10]
def points : Finset C13.Point := {1,3,7,10}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1371,1374,1395,1398,1402,1461,1509,1639,1651,1654,1693,1721,1753,1882,1894,1906,1945,1957,1969,2413,2421,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2861,2869,2873,2876,2901,2917,2921,2924,2929,2932,2936,2951,2963,2966,2979,2982,2986,2994,3011,3014,3026,3042,3127,3187,3190,3277,3292,3308,3379,3418,3442,3493,3532,3556,3623,3635,3686,3698,3725,3737,3788,3800,3854,3866,3878,3890,3980,3992,4004,4016]
def rows : List LinearRow := [⟨.covers 75,1,8⟩,⟨.covers 139,1,25⟩,⟨.covers 269,1,8⟩,⟨.covers 777,1,8⟩,⟨.covers 1289,1,17⟩,⟨.covers 3081,1,25⟩,⟨.covers 78,1,25⟩,⟨.covers 142,1,8⟩,⟨.covers 106,1,17⟩,⟨.covers 202,1,8⟩,⟨.covers 778,1,17⟩,⟨.covers 156,1,25⟩,⟨.covers 108,1,8⟩,⟨.covers 172,1,17⟩,⟨.covers 120,1,8⟩,⟨.covers 184,1,25⟩,⟨.covers 808,1,8⟩,⟨.covers 2376,1,8⟩,⟨.covers 3336,1,8⟩,⟨.covers 1728,1,25⟩,⟨.incident 3,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_006
namespace C13.Global.FastDual28_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,11]
def points : Finset C13.Point := {1,3,7,11}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1651,1653,1654,1693,1721,1753,1821,1845,1849,1852,1863,1875,1877,1878,1881,1882,1884,1891,1893,1894,1905,1906,1908,1912,1941,1945,1957,1969,1987,1989,2001,2017,2413,2421,2425,2455,2486,2518,2677,2731,2734,2746,2794,2901,2921,2929,2966,2986,2994,3127,3187,3189,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 519,1,5⟩,⟨.covers 2055,1,1⟩,⟨.covers 75,1,11⟩,⟨.covers 147,1,5⟩,⟨.covers 99,1,3⟩,⟨.covers 2307,1,4⟩,⟨.covers 1539,1,1⟩,⟨.covers 2563,1,4⟩,⟨.covers 141,1,1⟩,⟨.covers 525,1,2⟩,⟨.covers 2061,1,5⟩,⟨.covers 169,1,7⟩,⟨.covers 297,1,2⟩,⟨.covers 201,1,5⟩,⟨.covers 777,1,4⟩,⟨.covers 78,1,11⟩,⟨.covers 142,1,11⟩,⟨.covers 198,1,6⟩,⟨.covers 3078,1,5⟩,⟨.covers 154,1,7⟩,⟨.covers 106,1,3⟩,⟨.covers 2314,1,7⟩,⟨.covers 3082,1,11⟩,⟨.covers 114,1,4⟩,⟨.covers 178,1,4⟩,⟨.covers 226,1,4⟩,⟨.covers 1794,1,5⟩,⟨.covers 156,1,5⟩,⟨.covers 2316,1,4⟩,⟨.covers 1548,1,3⟩,⟨.covers 116,1,4⟩,⟨.covers 180,1,7⟩,⟨.covers 564,1,1⟩,⟨.covers 228,1,7⟩,⟨.covers 804,1,1⟩,⟨.covers 1572,1,2⟩,⟨.covers 2820,1,4⟩,⟨.covers 3588,1,4⟩,⟨.covers 120,1,4⟩,⟨.covers 1800,1,1⟩,⟨.covers 2824,1,4⟩,⟨.covers 3336,1,2⟩,⟨.covers 2160,1,4⟩,⟨.covers 1200,1,4⟩,⟨.covers 720,1,6⟩,⟨.covers 3216,1,6⟩,⟨.covers 2832,1,7⟩,⟨.covers 3600,1,7⟩,⟨.covers 1248,1,4⟩,⟨.covers 1824,1,2⟩,⟨.covers 3360,1,7⟩,⟨.covers 2496,1,5⟩,⟨.covers 2752,1,4⟩,⟨.covers 1920,1,5⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_007
