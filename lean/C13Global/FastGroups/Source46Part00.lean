import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source46
namespace C13.Global.FastDual46_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,8]
def points : Finset C13.Point := {1,3,6,8}
def columns : List Code := [254,506,701,743,758,829,949,956,967,979,995,1010,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1724,1766,1852,1882,1957,1972,1987,2002,2231,2285,2300,2413,2425,2455,2485,2486,2537,2552,2677,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2773,2789,2804,2861,2876,2921,2951,2966,2981,2996,3011,3041,3056,3127,3251,3253,3254,3277,3292,3308,3418,3433,3448,3478,3493,3508,3623,3635,3637,3638,3669,3685,3686,3700,3725,3733,3737,3740,3747,3749,3750,3753,3754,3756,3761,3762,3764,3768,3781,3788,3796,3812]
def rows : List LinearRow := [⟨.covers 75,1,25⟩,⟨.covers 139,1,25⟩,⟨.covers 147,1,12⟩,⟨.covers 2067,1,12⟩,⟨.covers 99,1,25⟩,⟨.covers 270,1,25⟩,⟨.covers 526,1,25⟩,⟨.covers 774,1,25⟩,⟨.covers 3078,1,12⟩,⟨.covers 778,1,12⟩,⟨.covers 2314,1,12⟩,⟨.covers 1546,1,12⟩,⟨.covers 114,1,25⟩,⟨.covers 3330,1,12⟩,⟨.covers 3586,1,12⟩,⟨.covers 1472,1,25⟩,⟨.incident 1,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source46.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source46.rootCodes link46 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual46_000
namespace C13.Global.FastDual46_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,9]
def points : Finset C13.Point := {1,3,6,9}
def columns : List Code := [254,506,701,743,758,829,953,956,967,979,995,1010,1371,1374,1402,1461,1498,1639,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2231,2285,2300,2413,2425,2455,2483,2485,2486,2537,2552,2677,2731,2734,2745,2746,2748,2773,2804,2876,2901,2986,3000,3011,3025,3056,3127,3251,3253,3254,3277,3292,3308,3351,3379,3381,3382,3405,3417,3418,3420,3433,3436,3448,3475,3477,3478,3493,3505,3506,3508,3529,3532,3544,3560,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 75,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 1728,1,1⟩,⟨.incident 1,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source46.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source46.rootCodes link46 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual46_001
namespace C13.Global.FastDual46_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,11]
def points : Finset C13.Point := {1,3,6,11}
def columns : List Code := [254,506,701,743,758,829,949,953,956,967,979,995,1010,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1724,1766,1821,1845,1849,1852,1863,1875,1878,1882,1891,1894,1906,1941,1945,1948,1957,1969,1972,1976,1987,1990,2002,2018,2231,2285,2300,2413,2425,2455,2483,2486,2537,2552,2677,2731,2734,2739,2742,2746,2773,2804,2901,2921,2929,2966,2986,2994,3056,3127,3251,3254,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 75,1,3⟩,⟨.covers 139,1,3⟩,⟨.covers 525,1,1⟩,⟨.covers 201,1,3⟩,⟨.covers 777,1,1⟩,⟨.covers 270,1,3⟩,⟨.covers 778,1,2⟩,⟨.covers 3082,1,3⟩,⟨.covers 2316,1,3⟩,⟨.covers 2572,1,2⟩,⟨.covers 568,1,1⟩,⟨.covers 216,1,2⟩,⟨.covers 664,1,1⟩,⟨.covers 3168,1,3⟩,⟨.incident 3,8,-3⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source46.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source46.rootCodes link46 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual46_002
namespace C13.Global.FastDual46_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,8]
def points : Finset C13.Point := {1,3,7,8}
def columns : List Code := [381,471,829,889,892,967,979,995,1143,1245,1371,1374,1401,1402,1404,1461,1509,1639,1651,1653,1654,1693,1721,1753,1852,1882,1912,1957,1987,2017,2413,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2861,2876,2921,2936,2951,2966,3011,3026,3127,3187,3189,3190,3277,3292,3308,3418,3433,3448,3478,3493,3508,3623,3635,3637,3638,3669,3683,3685,3686,3697,3698,3700,3725,3737,3740,3753,3754,3756,3768,3785,3788,3800,3816]
def rows : List LinearRow := [⟨.covers 1031,1,4⟩,⟨.covers 75,1,4⟩,⟨.covers 139,1,15⟩,⟨.covers 147,1,1⟩,⟨.covers 99,1,4⟩,⟨.covers 1283,1,11⟩,⟨.covers 2307,1,9⟩,⟨.covers 77,1,2⟩,⟨.covers 2117,1,3⟩,⟨.covers 537,1,3⟩,⟨.covers 201,1,1⟩,⟨.covers 777,1,4⟩,⟨.covers 3081,1,4⟩,⟨.covers 2097,1,3⟩,⟨.covers 3329,1,7⟩,⟨.covers 78,1,15⟩,⟨.covers 142,1,15⟩,⟨.covers 198,1,8⟩,⟨.covers 582,1,1⟩,⟨.covers 774,1,2⟩,⟨.covers 3078,1,4⟩,⟨.covers 106,1,7⟩,⟨.covers 202,1,8⟩,⟨.covers 778,1,7⟩,⟨.covers 2314,1,15⟩,⟨.covers 1546,1,8⟩,⟨.covers 114,1,4⟩,⟨.covers 178,1,11⟩,⟨.covers 3586,1,4⟩,⟨.covers 540,1,4⟩,⟨.covers 108,1,3⟩,⟨.covers 2124,1,2⟩,⟨.covers 2316,1,2⟩,⟨.covers 1548,1,4⟩,⟨.covers 212,1,1⟩,⟨.covers 2132,1,1⟩,⟨.covers 228,1,7⟩,⟨.covers 1604,1,3⟩,⟨.covers 120,1,4⟩,⟨.covers 184,1,4⟩,⟨.covers 216,1,7⟩,⟨.covers 2824,1,6⟩,⟨.covers 3592,1,4⟩,⟨.covers 1584,1,4⟩,⟨.covers 2256,1,1⟩,⟨.covers 912,1,9⟩,⟨.covers 1424,1,7⟩,⟨.covers 928,1,7⟩,⟨.covers 2880,1,1⟩,⟨.incident 1,8,-4⟩,⟨.incident 3,8,-4⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source46.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source46.rootCodes link46 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual46_003
namespace C13.Global.FastDual46_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,9]
def points : Finset C13.Point := {1,3,7,9}
def columns : List Code := [381,471,829,885,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1653,1654,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2413,2421,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2876,2901,2932,2986,3011,3042,3127,3187,3189,3190,3277,3292,3308,3351,3379,3381,3382,3405,3411,3413,3414,3417,3418,3420,3429,3433,3436,3441,3442,3444,3448,3477,3478,3493,3508,3525,3532,3540,3556,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,4⟩,⟨.covers 519,1,6⟩,⟨.covers 75,1,11⟩,⟨.covers 139,1,11⟩,⟨.covers 147,1,7⟩,⟨.covers 99,1,4⟩,⟨.covers 1059,1,2⟩,⟨.covers 141,1,7⟩,⟨.covers 297,1,2⟩,⟨.covers 201,1,4⟩,⟨.covers 777,1,7⟩,⟨.covers 2337,1,4⟩,⟨.covers 2817,1,11⟩,⟨.covers 3585,1,7⟩,⟨.covers 78,1,11⟩,⟨.covers 142,1,11⟩,⟨.covers 774,1,2⟩,⟨.covers 3078,1,6⟩,⟨.covers 154,1,11⟩,⟨.covers 202,1,4⟩,⟨.covers 778,1,7⟩,⟨.covers 114,1,6⟩,⟨.covers 226,1,7⟩,⟨.covers 1794,1,4⟩,⟨.covers 3330,1,6⟩,⟨.covers 3586,1,2⟩,⟨.covers 2316,1,6⟩,⟨.covers 1548,1,4⟩,⟨.covers 180,1,11⟩,⟨.covers 228,1,11⟩,⟨.covers 804,1,2⟩,⟨.covers 120,1,6⟩,⟨.covers 3336,1,6⟩,⟨.covers 624,1,4⟩,⟨.covers 1584,1,2⟩,⟨.covers 2256,1,11⟩,⟨.covers 912,1,4⟩,⟨.covers 1696,1,9⟩,⟨.covers 1824,1,4⟩,⟨.covers 2848,1,4⟩,⟨.covers 1728,1,7⟩,⟨.covers 3648,1,4⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source46.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source46.rootCodes link46 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual46_004
namespace C13.Global.FastDual46_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,11]
def points : Finset C13.Point := {1,3,7,11}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1651,1653,1654,1693,1721,1753,1821,1845,1849,1852,1863,1875,1877,1878,1881,1882,1884,1891,1893,1894,1905,1906,1908,1912,1941,1945,1957,1969,1987,1989,2001,2017,2413,2421,2425,2455,2486,2518,2677,2731,2734,2746,2794,2901,2921,2929,2966,2986,2994,3127,3187,3189,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 3648,1,1⟩,⟨.covers 1920,1,1⟩,⟨.covers 3456,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source46.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source46.rootCodes link46 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual46_005
namespace C13.Global.FastDual46_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,9,11]
def points : Finset C13.Point := {1,3,9,11}
def columns : List Code := [247,251,253,254,381,471,499,501,502,505,506,508,701,743,755,757,758,761,762,764,829,885,892,953,956,967,979,981,995,998,1009,1010,1012,1016,1143,1245,1267,1269,1270,1273,1274,1276,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1491,1493,1494,1497,1498,1500,1509,1521,1522,1524,1528,1639,1653,1654,1693,1721,1724,1749,1753,1763,1766,1777,1778,1780,1784,1821,1852,1863,1877,1894,1908,1945,1976,1987,2001,2018,2032,2231,2285,2291,2293,2294,2297,2298,2300,2413,2421,2425,2455,2483,2486,2517,2518,2537,2540,2545,2546,2548,2552,2677,2731,2734,2746,2773,2794,2801,2802,2804,2808,2901,2986,3056,3127,3187,3189,3251,3254,3277,3285,3292,3305,3308,3313,3314,3316,3320,3351,3379,3405,3413,3433,3441,3478,3506,3532,3540,3560,3568,3669,3754,3824]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 267,1,2⟩,⟨.covers 523,1,2⟩,⟨.covers 1539,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 417,1,1⟩,⟨.covers 2817,1,2⟩,⟨.covers 3585,1,2⟩,⟨.covers 270,1,2⟩,⟨.covers 526,1,2⟩,⟨.covers 3078,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 778,1,2⟩,⟨.covers 1546,1,2⟩,⟨.covers 3330,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 1188,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 1824,1,1⟩,⟨.covers 2752,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source46.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source46.rootCodes link46 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual46_006
namespace C13.Global.FastDual46_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,8]
def points : Finset C13.Point := {1,6,7,8}
def columns : List Code := [829,967,971,979,995,1150,1213,1341,1371,1374,1402,1453,1461,1597,1639,1646,1654,1693,1709,1721,1837,1852,1867,1882,1957,1987,2173,2238,2365,2413,2425,2455,2462,2486,2621,2653,2669,2677,2731,2734,2746,2861,2876,2921,2951,2966,3011,3127,3131,3133,3134,3165,3181,3196,3229,3245,3260,3277,3292,3308,3358,3373,3388,3418,3433,3448,3478,3493,3508,3613,3623,3627,3629,3630,3635,3637,3638,3641,3642,3644,3661,3669,3676,3685,3686,3692,3700,3725,3737,3740,3753,3754,3756,3768,3788]
def rows : List LinearRow := [⟨.covers 1031,1,8⟩,⟨.covers 1035,1,8⟩,⟨.covers 147,1,6⟩,⟨.covers 2067,1,3⟩,⟨.covers 163,1,8⟩,⟨.covers 77,1,6⟩,⟨.covers 141,1,6⟩,⟨.covers 269,1,3⟩,⟨.covers 149,1,3⟩,⟨.covers 101,1,3⟩,⟨.covers 89,1,3⟩,⟨.covers 169,1,3⟩,⟨.covers 1553,1,3⟩,⟨.covers 2577,1,3⟩,⟨.covers 3329,1,8⟩,⟨.covers 142,1,3⟩,⟨.covers 526,1,8⟩,⟨.covers 86,1,8⟩,⟨.covers 774,1,11⟩,⟨.covers 1286,1,3⟩,⟨.covers 154,1,8⟩,⟨.covers 106,1,3⟩,⟨.covers 202,1,11⟩,⟨.covers 3330,1,8⟩,⟨.covers 3586,1,3⟩,⟨.covers 212,1,11⟩,⟨.covers 228,1,11⟩,⟨.covers 792,1,3⟩,⟨.covers 1800,1,3⟩,⟨.covers 2824,1,8⟩,⟨.covers 368,1,8⟩,⟨.covers 624,1,3⟩,⟨.covers 432,1,8⟩,⟨.covers 688,1,3⟩,⟨.covers 848,1,6⟩,⟨.covers 2656,1,3⟩,⟨.covers 928,1,3⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,3⟩,⟨.covers 1824,1,6⟩,⟨.covers 1472,1,11⟩,⟨.covers 2496,1,11⟩,⟨.covers 3392,1,3⟩,⟨.covers 3648,1,6⟩,⟨.covers 3712,1,6⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source46.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source46.rootCodes link46 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual46_007
