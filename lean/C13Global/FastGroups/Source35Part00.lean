import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source35
namespace C13.Global.FastDual35_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,9]
def points : Finset C13.Point := {1,3,6,9}
def columns : List Code := [701,743,829,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2231,2285,2413,2425,2455,2483,2485,2486,2537,2677,2731,2734,2745,2746,2748,2773,2876,2901,2986,3000,3011,3025,3127,3251,3253,3254,3277,3292,3308,3351,3379,3381,3382,3405,3417,3418,3420,3433,3436,3448,3475,3477,3478,3493,3505,3506,3508,3529,3532,3544,3560,3669,3686,3700,3737,3754,3768,3851,3865,3882,3896,3907,3921,3938,3952]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,2⟩,⟨.covers 83,1,1⟩,⟨.covers 99,1,2⟩,⟨.covers 78,1,2⟩,⟨.covers 142,1,1⟩,⟨.covers 774,1,2⟩,⟨.covers 2566,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 1546,1,2⟩,⟨.covers 114,1,2⟩,⟨.covers 178,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 2434,1,1⟩,⟨.covers 1728,1,2⟩,⟨.incident 1,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source35.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source35.rootCodes link35 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual35_000
namespace C13.Global.FastDual35_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,10]
def points : Finset C13.Point := {1,3,6,10}
def columns : List Code := [701,743,829,949,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1766,1882,1894,1906,1945,1957,1969,2231,2285,2413,2425,2455,2483,2485,2486,2537,2677,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2773,2789,2861,2869,2873,2876,2901,2917,2921,2929,2951,2963,2965,2966,2979,2981,2982,2985,2986,2988,2993,2994,2996,3000,3011,3013,3025,3041,3127,3251,3253,3277,3292,3308,3379,3418,3493,3505,3532,3544,3623,3635,3686,3725,3737,3749,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 83,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 1793,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 3648,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source35.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source35.rootCodes link35 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual35_001
namespace C13.Global.FastDual35_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,11]
def points : Finset C13.Point := {1,3,6,11}
def columns : List Code := [701,743,829,949,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1724,1766,1821,1845,1849,1852,1863,1875,1878,1882,1891,1894,1906,1941,1945,1948,1957,1969,1972,1976,1987,1990,2002,2018,2231,2285,2413,2425,2455,2483,2486,2537,2677,2731,2734,2739,2742,2746,2773,2901,2921,2929,2966,2986,2994,3127,3251,3254,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,17⟩,⟨.covers 83,1,2⟩,⟨.covers 147,1,4⟩,⟨.covers 99,1,2⟩,⟨.covers 387,1,1⟩,⟨.covers 1539,1,2⟩,⟨.covers 525,1,3⟩,⟨.covers 1061,1,1⟩,⟨.covers 389,1,1⟩,⟨.covers 89,1,13⟩,⟨.covers 201,1,11⟩,⟨.covers 1161,1,2⟩,⟨.covers 777,1,3⟩,⟨.covers 3105,1,1⟩,⟨.covers 1665,1,2⟩,⟨.covers 2817,1,3⟩,⟨.covers 3329,1,2⟩,⟨.covers 3585,1,5⟩,⟨.covers 78,1,10⟩,⟨.covers 142,1,6⟩,⟨.covers 1062,1,2⟩,⟨.covers 390,1,2⟩,⟨.covers 774,1,3⟩,⟨.covers 3078,1,2⟩,⟨.covers 106,1,16⟩,⟨.covers 202,1,16⟩,⟨.covers 2314,1,10⟩,⟨.covers 3082,1,17⟩,⟨.covers 178,1,4⟩,⟨.covers 226,1,5⟩,⟨.covers 1794,1,2⟩,⟨.covers 3330,1,4⟩,⟨.covers 92,1,6⟩,⟨.covers 156,1,2⟩,⟨.covers 108,1,2⟩,⟨.covers 2316,1,11⟩,⟨.covers 1548,1,3⟩,⟨.covers 2572,1,11⟩,⟨.covers 116,1,5⟩,⟨.covers 308,1,2⟩,⟨.covers 212,1,5⟩,⟨.covers 184,1,3⟩,⟨.covers 568,1,4⟩,⟨.covers 1800,1,4⟩,⟨.covers 2824,1,7⟩,⟨.covers 1584,1,1⟩,⟨.covers 912,1,1⟩,⟨.covers 2832,1,2⟩,⟨.covers 1248,1,1⟩,⟨.covers 3168,1,11⟩,⟨.covers 2496,1,2⟩,⟨.incident 1,8,-3⟩,⟨.incident 3,8,-8⟩,⟨.incident 11,8,-1⟩]
def bound : Int := 6

theorem column_mask : listMask columns = restrictMask universeMask Source35.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source35.rootCodes link35 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual35_002
namespace C13.Global.FastDual35_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,9,11]
def points : Finset C13.Point := {1,3,9,11}
def columns : List Code := [247,251,253,254,381,471,499,501,502,505,506,508,701,743,755,757,758,761,762,764,829,885,892,953,956,967,979,981,995,998,1009,1010,1012,1016,1143,1245,1267,1269,1270,1273,1274,1276,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1491,1493,1494,1497,1498,1500,1509,1521,1522,1524,1528,1639,1653,1654,1693,1721,1724,1749,1753,1763,1766,1777,1778,1780,1784,1821,1852,1863,1877,1894,1908,1945,1976,1987,2001,2018,2032,2231,2285,2291,2293,2294,2297,2298,2300,2413,2421,2425,2455,2483,2486,2517,2518,2537,2540,2545,2546,2548,2552,2677,2731,2734,2746,2773,2794,2801,2802,2804,2808,2901,2986,3056,3127,3187,3189,3251,3254,3277,3285,3292,3305,3308,3313,3314,3316,3320,3351,3379,3405,3413,3433,3441,3478,3506,3532,3540,3560,3568,3669,3754,3824]
def rows : List LinearRow := [⟨.covers 135,1,8⟩,⟨.covers 519,1,4⟩,⟨.covers 2055,1,3⟩,⟨.covers 267,1,19⟩,⟨.covers 523,1,19⟩,⟨.covers 147,1,4⟩,⟨.covers 99,1,2⟩,⟨.covers 2307,1,1⟩,⟨.covers 1539,1,8⟩,⟨.covers 141,1,7⟩,⟨.covers 525,1,5⟩,⟨.covers 2061,1,5⟩,⟨.covers 297,1,2⟩,⟨.covers 201,1,2⟩,⟨.covers 777,1,10⟩,⟨.covers 3081,1,1⟩,⟨.covers 2097,1,3⟩,⟨.covers 657,1,3⟩,⟨.covers 2145,1,3⟩,⟨.covers 1185,1,8⟩,⟨.covers 2817,1,19⟩,⟨.covers 3585,1,19⟩,⟨.covers 270,1,19⟩,⟨.covers 526,1,19⟩,⟨.covers 1062,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 3078,1,13⟩,⟨.covers 154,1,4⟩,⟨.covers 106,1,7⟩,⟨.covers 778,1,19⟩,⟨.covers 1546,1,19⟩,⟨.covers 402,1,1⟩,⟨.covers 2194,1,2⟩,⟨.covers 610,1,1⟩,⟨.covers 450,1,5⟩,⟨.covers 1794,1,6⟩,⟨.covers 3330,1,2⟩,⟨.covers 156,1,2⟩,⟨.covers 108,1,2⟩,⟨.covers 2316,1,7⟩,⟨.covers 1548,1,2⟩,⟨.covers 116,1,4⟩,⟨.covers 564,1,1⟩,⟨.covers 612,1,3⟩,⟨.covers 420,1,8⟩,⟨.covers 1188,1,3⟩,⟨.covers 312,1,2⟩,⟨.covers 664,1,1⟩,⟨.covers 1224,1,4⟩,⟨.covers 2248,1,1⟩,⟨.covers 1800,1,4⟩,⟨.covers 3336,1,6⟩,⟨.covers 2352,1,6⟩,⟨.covers 1584,1,4⟩,⟨.covers 1232,1,4⟩,⟨.covers 912,1,2⟩,⟨.covers 2704,1,11⟩,⟨.covers 3216,1,1⟩,⟨.covers 1824,1,7⟩,⟨.covers 3360,1,7⟩,⟨.covers 2496,1,1⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source35.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source35.rootCodes link35 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual35_003
namespace C13.Global.FastDual35_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,9,10]
def points : Finset C13.Point := {1,6,9,10}
def columns : List Code := [445,475,701,743,829,925,953,956,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1465,1498,1639,1646,1654,1693,1721,1766,1894,1945,2173,2231,2235,2237,2238,2269,2285,2365,2397,2413,2425,2455,2459,2461,2462,2477,2483,2485,2486,2489,2490,2492,2509,2521,2537,2621,2653,2677,2717,2731,2734,2745,2746,2748,2773,2845,2876,2901,2955,2969,2986,3000,3011,3025,3127,3131,3229,3245,3251,3253,3257,3277,3292,3308,3355,3379,3418,3469,3481,3493,3505,3532,3544,3686,3737]
def rows : List LinearRow := [⟨.covers 263,1,1⟩,⟨.covers 1031,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 1539,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 1793,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 86,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 688,1,1⟩,⟨.covers 1328,1,1⟩,⟨.covers 848,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 3392,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source35.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source35.rootCodes link35 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual35_004
namespace C13.Global.FastDual35_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,9,11]
def points : Finset C13.Point := {1,6,9,11}
def columns : List Code := [445,475,701,743,829,925,953,956,967,971,979,995,1150,1213,1341,1371,1374,1402,1437,1453,1461,1465,1468,1498,1597,1639,1646,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2173,2231,2235,2238,2269,2285,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2653,2677,2731,2734,2746,2773,2901,2986,3127,3131,3165,3181,3251,3254,3258,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 2055,1,4⟩,⟨.covers 75,1,1⟩,⟨.covers 523,1,8⟩,⟨.covers 1035,1,5⟩,⟨.covers 147,1,2⟩,⟨.covers 99,1,9⟩,⟨.covers 1539,1,4⟩,⟨.covers 2563,1,9⟩,⟨.covers 77,1,2⟩,⟨.covers 525,1,4⟩,⟨.covers 201,1,1⟩,⟨.covers 777,1,4⟩,⟨.covers 3081,1,3⟩,⟨.covers 1169,1,4⟩,⟨.covers 2337,1,1⟩,⟨.covers 3105,1,1⟩,⟨.covers 2817,1,9⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,5⟩,⟨.covers 270,1,6⟩,⟨.covers 390,1,2⟩,⟨.covers 774,1,9⟩,⟨.covers 2566,1,7⟩,⟨.covers 3078,1,4⟩,⟨.covers 106,1,6⟩,⟨.covers 1546,1,4⟩,⟨.covers 210,1,2⟩,⟨.covers 2818,1,16⟩,⟨.covers 3586,1,13⟩,⟨.covers 300,1,4⟩,⟨.covers 2316,1,1⟩,⟨.covers 1548,1,4⟩,⟨.covers 2572,1,9⟩,⟨.covers 228,1,2⟩,⟨.covers 1220,1,1⟩,⟨.covers 232,1,2⟩,⟨.covers 688,1,4⟩,⟨.covers 2352,1,6⟩,⟨.covers 1584,1,4⟩,⟨.covers 2608,1,12⟩,⟨.covers 1232,1,3⟩,⟨.covers 848,1,5⟩,⟨.covers 1616,1,9⟩,⟨.covers 912,1,4⟩,⟨.covers 3216,1,2⟩,⟨.covers 864,1,4⟩,⟨.covers 2656,1,2⟩,⟨.covers 3168,1,1⟩,⟨.covers 2496,1,3⟩,⟨.covers 1728,1,9⟩,⟨.covers 2752,1,14⟩,⟨.incident 1,8,-2⟩,⟨.incident 9,8,-7⟩,⟨.incident 11,8,-3⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source35.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source35.rootCodes link35 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual35_005
namespace C13.Global.FastDual35_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,10,11]
def points : Finset C13.Point := {1,6,10,11}
def columns : List Code := [445,475,701,743,829,925,941,949,953,956,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1465,1498,1639,1646,1654,1693,1709,1717,1721,1766,1870,1882,1894,1906,1933,1945,1957,1969,2173,2231,2235,2238,2269,2285,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2653,2669,2677,2731,2734,2739,2742,2746,2765,2773,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3251,3277,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 263,1,6⟩,⟨.covers 75,1,1⟩,⟨.covers 523,1,5⟩,⟨.covers 99,1,6⟩,⟨.covers 1283,1,5⟩,⟨.covers 77,1,3⟩,⟨.covers 1037,1,4⟩,⟨.covers 293,1,3⟩,⟨.covers 2309,1,2⟩,⟨.covers 1541,1,4⟩,⟨.covers 89,1,1⟩,⟨.covers 537,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 1289,1,4⟩,⟨.covers 2569,1,3⟩,⟨.covers 3081,1,8⟩,⟨.covers 3329,1,10⟩,⟨.covers 3585,1,15⟩,⟨.covers 142,1,6⟩,⟨.covers 86,1,10⟩,⟨.covers 1286,1,1⟩,⟨.covers 2566,1,3⟩,⟨.covers 3078,1,15⟩,⟨.covers 154,1,3⟩,⟨.covers 554,1,1⟩,⟨.covers 1546,1,10⟩,⟨.covers 3082,1,7⟩,⟨.covers 210,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 788,1,2⟩,⟨.covers 2324,1,1⟩,⟨.covers 2580,1,2⟩,⟨.covers 120,1,1⟩,⟨.covers 568,1,1⟩,⟨.covers 664,1,2⟩,⟨.covers 360,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 3336,1,11⟩,⟨.covers 3592,1,14⟩,⟨.covers 2160,1,4⟩,⟨.covers 1200,1,3⟩,⟨.covers 720,1,5⟩,⟨.covers 2384,1,2⟩,⟨.covers 1616,1,1⟩,⟨.covers 3152,1,14⟩,⟨.covers 1424,1,4⟩,⟨.covers 2704,1,3⟩,⟨.covers 1248,1,8⟩,⟨.covers 1376,1,8⟩,⟨.covers 2656,1,4⟩,⟨.covers 2464,1,7⟩,⟨.covers 1696,1,3⟩,⟨.covers 3232,1,6⟩,⟨.covers 1824,1,1⟩,⟨.covers 1472,1,4⟩,⟨.incident 10,8,-5⟩,⟨.incident 11,8,-4⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source35.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source35.rootCodes link35 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual35_006
namespace C13.Global.FastDual35_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,9,10]
def points : Finset C13.Point := {3,6,9,10}
def columns : List Code := [379,439,631,699,701,702,727,743,829,830,855,871,953,954,956,967,979,995,1207,1246,1335,1371,1374,1402,1447,1459,1461,1498,1639,1654,1691,1693,1721,1766,1894,1945,2231,2285,2359,2411,2413,2425,2455,2471,2483,2485,2486,2537,2647,2663,2677,2731,2734,2745,2746,2748,2759,2773,2862,2876,2887,2901,2986,3000,3011,3025,3127,3239,3251,3253,3277,3278,3292,3308,3367,3379,3406,3418,3493,3505,3532,3544,3686,3737]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 1031,1,4⟩,⟨.covers 75,1,2⟩,⟨.covers 1035,1,9⟩,⟨.covers 2059,1,5⟩,⟨.covers 1283,1,4⟩,⟨.covers 2563,1,3⟩,⟨.covers 269,1,7⟩,⟨.covers 389,1,4⟩,⟨.covers 3077,1,4⟩,⟨.covers 201,1,7⟩,⟨.covers 1793,1,17⟩,⟨.covers 2817,1,1⟩,⟨.covers 3585,1,17⟩,⟨.covers 526,1,5⟩,⟨.covers 778,1,2⟩,⟨.covers 1546,1,8⟩,⟨.covers 3082,1,14⟩,⟨.covers 2098,1,4⟩,⟨.covers 898,1,1⟩,⟨.covers 2690,1,2⟩,⟨.covers 1794,1,13⟩,⟨.covers 3586,1,3⟩,⟨.covers 92,1,11⟩,⟨.covers 284,1,3⟩,⟨.covers 1548,1,17⟩,⟨.covers 2572,1,3⟩,⟨.covers 212,1,3⟩,⟨.covers 2580,1,2⟩,⟨.covers 120,1,5⟩,⟨.covers 184,1,2⟩,⟨.covers 2160,1,2⟩,⟨.covers 1200,1,4⟩,⟨.covers 1328,1,4⟩,⟨.covers 2608,1,3⟩,⟨.covers 720,1,2⟩,⟨.covers 848,1,4⟩,⟨.covers 1616,1,13⟩,⟨.covers 3168,1,11⟩,⟨.covers 928,1,5⟩,⟨.covers 3232,1,4⟩,⟨.covers 1472,1,14⟩,⟨.covers 1728,1,13⟩,⟨.incident 3,8,-4⟩,⟨.incident 9,8,-3⟩,⟨.incident 10,8,-7⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source35.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source35.rootCodes link35 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual35_007
