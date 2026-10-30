import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source18
namespace C13.Global.FastDual18_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,8]
def points : Finset C13.Point := {1,3,7,8}
def columns : List Code := [381,471,829,889,892,967,979,995,1143,1245,1371,1374,1401,1402,1404,1461,1509,1639,1651,1653,1654,1693,1721,1753,1852,1882,1912,1957,1987,2017,2413,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2861,2876,2921,2936,2951,2966,3011,3026,3127,3187,3189,3190,3277,3292,3308,3418,3433,3448,3478,3493,3508,3623,3635,3637,3638,3669,3683,3685,3686,3697,3698,3700,3725,3737,3740,3753,3754,3756,3768,3785,3788,3800,3816]
def rows : List LinearRow := [⟨.covers 139,1,2⟩,⟨.covers 147,1,2⟩,⟨.covers 99,1,1⟩,⟨.covers 1283,1,2⟩,⟨.covers 78,1,2⟩,⟨.covers 142,1,2⟩,⟨.covers 774,1,2⟩,⟨.covers 3078,1,1⟩,⟨.covers 202,1,2⟩,⟨.covers 778,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 178,1,2⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 2496,1,2⟩,⟨.incident 1,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source18.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source18.rootCodes link18 points rows bound = true := by decide +kernel

end C13.Global.FastDual18_000
namespace C13.Global.FastDual18_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,9]
def points : Finset C13.Point := {1,3,7,9}
def columns : List Code := [381,471,829,885,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1653,1654,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2413,2421,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2876,2901,2932,2986,3011,3042,3127,3187,3189,3190,3277,3292,3308,3351,3379,3381,3382,3405,3411,3413,3414,3417,3418,3420,3429,3433,3436,3441,3442,3444,3448,3477,3478,3493,3508,3525,3532,3540,3556,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 519,1,10⟩,⟨.covers 2055,1,1⟩,⟨.covers 75,1,12⟩,⟨.covers 139,1,12⟩,⟨.covers 147,1,9⟩,⟨.covers 99,1,1⟩,⟨.covers 141,1,10⟩,⟨.covers 525,1,1⟩,⟨.covers 2061,1,2⟩,⟨.covers 297,1,1⟩,⟨.covers 777,1,9⟩,⟨.covers 2097,1,2⟩,⟨.covers 2577,1,1⟩,⟨.covers 417,1,1⟩,⟨.covers 2337,1,2⟩,⟨.covers 3105,1,2⟩,⟨.covers 78,1,12⟩,⟨.covers 142,1,4⟩,⟨.covers 166,1,1⟩,⟨.covers 2566,1,6⟩,⟨.covers 3078,1,5⟩,⟨.covers 154,1,10⟩,⟨.covers 202,1,5⟩,⟨.covers 778,1,8⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,12⟩,⟨.covers 114,1,6⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,7⟩,⟨.covers 1794,1,1⟩,⟨.covers 2818,1,2⟩,⟨.covers 3330,1,4⟩,⟨.covers 156,1,1⟩,⟨.covers 108,1,4⟩,⟨.covers 2316,1,1⟩,⟨.covers 2820,1,10⟩,⟨.covers 120,1,6⟩,⟨.covers 184,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3336,1,6⟩,⟨.covers 624,1,1⟩,⟨.covers 432,1,10⟩,⟨.covers 2256,1,10⟩,⟨.covers 912,1,1⟩,⟨.covers 3600,1,10⟩,⟨.covers 480,1,2⟩,⟨.covers 1248,1,7⟩,⟨.covers 1824,1,10⟩,⟨.covers 1728,1,10⟩,⟨.covers 3456,1,1⟩,⟨.incident 3,8,-1⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source18.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source18.rootCodes link18 points rows bound = true := by decide +kernel

end C13.Global.FastDual18_001
namespace C13.Global.FastDual18_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,10]
def points : Finset C13.Point := {1,3,7,10}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1371,1374,1395,1398,1402,1461,1509,1639,1651,1654,1693,1721,1753,1882,1894,1906,1945,1957,1969,2413,2421,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2861,2869,2873,2876,2901,2917,2921,2924,2929,2932,2936,2951,2963,2966,2979,2982,2986,2994,3011,3014,3026,3042,3127,3187,3190,3277,3292,3308,3379,3418,3442,3493,3532,3556,3623,3635,3686,3698,3725,3737,3788,3800,3854,3866,3878,3890,3980,3992,4004,4016]
def rows : List LinearRow := [⟨.covers 75,1,8⟩,⟨.covers 139,1,25⟩,⟨.covers 269,1,8⟩,⟨.covers 777,1,8⟩,⟨.covers 1289,1,17⟩,⟨.covers 3081,1,25⟩,⟨.covers 78,1,25⟩,⟨.covers 142,1,8⟩,⟨.covers 106,1,17⟩,⟨.covers 202,1,8⟩,⟨.covers 2314,1,17⟩,⟨.covers 1546,1,8⟩,⟨.covers 156,1,25⟩,⟨.covers 108,1,8⟩,⟨.covers 172,1,17⟩,⟨.covers 120,1,8⟩,⟨.covers 184,1,25⟩,⟨.covers 808,1,8⟩,⟨.covers 2376,1,8⟩,⟨.covers 1728,1,25⟩,⟨.incident 3,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source18.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source18.rootCodes link18 points rows bound = true := by decide +kernel

end C13.Global.FastDual18_002
namespace C13.Global.FastDual18_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,11]
def points : Finset C13.Point := {1,3,7,11}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1651,1653,1654,1693,1721,1753,1821,1845,1849,1852,1863,1875,1877,1878,1881,1882,1884,1891,1893,1894,1905,1906,1908,1912,1941,1945,1957,1969,1987,1989,2001,2017,2413,2421,2425,2455,2486,2518,2677,2731,2734,2746,2794,2901,2921,2929,2966,2986,2994,3127,3187,3189,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 2307,1,1⟩,⟨.covers 1539,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 1062,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 300,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 480,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 3456,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source18.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source18.rootCodes link18 points rows bound = true := by decide +kernel

end C13.Global.FastDual18_003
namespace C13.Global.FastDual18_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,8,10]
def points : Finset C13.Point := {1,3,8,10}
def columns : List Code := [247,251,253,254,381,471,499,501,502,505,506,508,701,743,755,757,758,761,762,764,829,889,892,949,956,967,979,982,995,997,1009,1010,1012,1016,1143,1245,1267,1269,1270,1273,1274,1276,1371,1374,1402,1461,1498,1509,1521,1522,1524,1528,1639,1651,1654,1693,1717,1721,1753,1756,1765,1766,1777,1778,1780,1784,1882,1957,2032,2231,2285,2291,2293,2294,2297,2298,2300,2413,2425,2428,2455,2485,2486,2515,2518,2533,2537,2545,2546,2548,2552,2677,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2773,2787,2789,2790,2793,2794,2796,2801,2802,2804,2808,2861,2876,2921,2936,2951,2966,2981,2996,3011,3026,3041,3056,3127,3187,3190,3251,3253,3277,3289,3292,3301,3308,3313,3314,3316,3320,3418,3493,3568,3623,3635,3686,3698,3725,3737,3749,3761,3788,3800,3812,3824]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 263,1,4⟩,⟨.covers 1031,1,5⟩,⟨.covers 267,1,19⟩,⟨.covers 523,1,19⟩,⟨.covers 147,1,2⟩,⟨.covers 99,1,4⟩,⟨.covers 579,1,1⟩,⟨.covers 2307,1,8⟩,⟨.covers 1539,1,1⟩,⟨.covers 77,1,2⟩,⟨.covers 269,1,5⟩,⟨.covers 1037,1,5⟩,⟨.covers 201,1,6⟩,⟨.covers 2121,1,1⟩,⟨.covers 777,1,8⟩,⟨.covers 3081,1,1⟩,⟨.covers 1073,1,4⟩,⟨.covers 593,1,5⟩,⟨.covers 2129,1,5⟩,⟨.covers 1169,1,3⟩,⟨.covers 270,1,19⟩,⟨.covers 526,1,19⟩,⟨.covers 198,1,6⟩,⟨.covers 582,1,1⟩,⟨.covers 774,1,2⟩,⟨.covers 3078,1,8⟩,⟨.covers 106,1,2⟩,⟨.covers 202,1,6⟩,⟨.covers 778,1,19⟩,⟨.covers 2314,1,19⟩,⟨.covers 2098,1,2⟩,⟨.covers 2194,1,2⟩,⟨.covers 610,1,1⟩,⟨.covers 1122,1,4⟩,⟨.covers 450,1,1⟩,⟨.covers 706,1,2⟩,⟨.covers 2818,1,6⟩,⟨.covers 3586,1,5⟩,⟨.covers 156,1,2⟩,⟨.covers 108,1,4⟩,⟨.covers 2124,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 1548,1,7⟩,⟨.covers 308,1,4⟩,⟨.covers 596,1,5⟩,⟨.covers 2132,1,5⟩,⟨.covers 404,1,3⟩,⟨.covers 1796,1,19⟩,⟨.covers 3332,1,19⟩,⟨.covers 568,1,2⟩,⟨.covers 664,1,2⟩,⟨.covers 360,1,4⟩,⟨.covers 2152,1,1⟩,⟨.covers 1224,1,1⟩,⟨.covers 2248,1,2⟩,⟨.covers 2824,1,5⟩,⟨.covers 3592,1,6⟩,⟨.covers 688,1,3⟩,⟨.covers 2224,1,2⟩,⟨.covers 1424,1,4⟩,⟨.covers 2832,1,7⟩,⟨.covers 3600,1,7⟩,⟨.covers 736,1,2⟩,⟨.covers 2272,1,3⟩,⟨.covers 864,1,1⟩,⟨.covers 1472,1,7⟩,⟨.covers 2496,1,2⟩,⟨.covers 1728,1,2⟩]
def bound : Int := 20

theorem column_mask : listMask columns = restrictMask universeMask Source18.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source18.rootCodes link18 points rows bound = true := by decide +kernel

end C13.Global.FastDual18_004
namespace C13.Global.FastDual18_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,9,11]
def points : Finset C13.Point := {1,3,9,11}
def columns : List Code := [247,251,253,254,381,471,499,501,502,505,506,508,701,743,755,757,758,761,762,764,829,885,892,953,956,967,979,981,995,998,1009,1010,1012,1016,1143,1245,1267,1269,1270,1273,1274,1276,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1491,1493,1494,1497,1498,1500,1509,1521,1522,1524,1528,1639,1653,1654,1693,1721,1724,1749,1753,1763,1766,1777,1778,1780,1784,1821,1852,1863,1877,1894,1908,1945,1976,1987,2001,2018,2032,2231,2285,2291,2293,2294,2297,2298,2300,2413,2421,2425,2455,2483,2486,2517,2518,2537,2540,2545,2546,2548,2552,2677,2731,2734,2746,2773,2794,2801,2802,2804,2808,2901,2986,3056,3127,3187,3189,3251,3254,3277,3285,3292,3305,3308,3313,3314,3316,3320,3351,3379,3405,3413,3433,3441,3478,3506,3532,3540,3560,3568,3669,3754,3824]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 267,1,2⟩,⟨.covers 523,1,2⟩,⟨.covers 147,1,1⟩,⟨.covers 1539,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 417,1,1⟩,⟨.covers 270,1,2⟩,⟨.covers 526,1,2⟩,⟨.covers 3078,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 778,1,2⟩,⟨.covers 1546,1,2⟩,⟨.covers 156,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 1188,1,1⟩,⟨.covers 2820,1,2⟩,⟨.covers 3588,1,2⟩,⟨.covers 1824,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source18.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source18.rootCodes link18 points rows bound = true := by decide +kernel

end C13.Global.FastDual18_005
namespace C13.Global.FastDual18_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,8,9]
def points : Finset C13.Point := {1,7,8,9}
def columns : List Code := [381,471,637,747,829,892,967,971,979,995,1143,1147,1149,1150,1213,1245,1261,1341,1371,1374,1389,1401,1402,1404,1453,1461,1509,1597,1629,1639,1646,1653,1654,1660,1693,1721,1753,1852,1987,2173,2238,2365,2413,2425,2428,2455,2462,2486,2518,2621,2653,2677,2684,2731,2734,2746,2794,2876,3011,3127,3131,3133,3134,3165,3181,3187,3189,3190,3193,3194,3196,3229,3245,3260,3277,3292,3308,3358,3373,3388,3418,3433,3448,3478,3493,3508,3613,3630,3644,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 1031,1,8⟩,⟨.covers 2055,1,3⟩,⟨.covers 1035,1,8⟩,⟨.covers 2059,1,3⟩,⟨.covers 141,1,4⟩,⟨.covers 525,1,3⟩,⟨.covers 773,1,8⟩,⟨.covers 2309,1,8⟩,⟨.covers 1541,1,3⟩,⟨.covers 169,1,3⟩,⟨.covers 1289,1,3⟩,⟨.covers 2569,1,5⟩,⟨.covers 2129,1,3⟩,⟨.covers 1169,1,1⟩,⟨.covers 2145,1,3⟩,⟨.covers 1185,1,1⟩,⟨.covers 78,1,8⟩,⟨.covers 142,1,11⟩,⟨.covers 198,1,2⟩,⟨.covers 774,1,1⟩,⟨.covers 1286,1,3⟩,⟨.covers 778,1,11⟩,⟨.covers 1546,1,3⟩,⟨.covers 114,1,3⟩,⟨.covers 1794,1,9⟩,⟨.covers 2818,1,11⟩,⟨.covers 3330,1,8⟩,⟨.covers 3586,1,8⟩,⟨.covers 1796,1,11⟩,⟨.covers 2820,1,11⟩,⟨.covers 216,1,4⟩,⟨.covers 368,1,3⟩,⟨.covers 624,1,3⟩,⟨.covers 432,1,9⟩,⟨.covers 688,1,6⟩,⟨.covers 2256,1,6⟩,⟨.covers 848,1,5⟩,⟨.covers 2384,1,3⟩,⟨.covers 1616,1,5⟩,⟨.covers 912,1,5⟩,⟨.covers 2704,1,4⟩,⟨.covers 1248,1,3⟩,⟨.covers 2272,1,8⟩,⟨.covers 1376,1,5⟩,⟨.covers 2656,1,3⟩,⟨.covers 928,1,11⟩,⟨.covers 2464,1,2⟩,⟨.covers 1472,1,2⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source18.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source18.rootCodes link18 points rows bound = true := by decide +kernel

end C13.Global.FastDual18_006
namespace C13.Global.FastDual18_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,8,10]
def points : Finset C13.Point := {1,7,8,10}
def columns : List Code := [381,471,637,747,829,877,889,892,967,971,979,995,1143,1147,1150,1213,1245,1261,1371,1374,1402,1453,1461,1509,1639,1646,1651,1654,1658,1693,1709,1721,1741,1753,1882,1957,2173,2238,2365,2413,2425,2428,2455,2462,2486,2518,2621,2653,2669,2677,2681,2684,2731,2734,2746,2794,2861,2876,2921,2936,2951,2966,3011,3026,3127,3131,3187,3190,3194,3229,3245,3277,3292,3308,3418,3493,3623,3635,3686,3698,3725,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 1289,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 3332,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 688,1,1⟩,⟨.covers 1328,1,1⟩,⟨.covers 1584,1,1⟩,⟨.covers 2272,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 1728,1,1⟩,⟨.incident 10,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source18.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source18.rootCodes link18 points rows bound = true := by decide +kernel

end C13.Global.FastDual18_007
