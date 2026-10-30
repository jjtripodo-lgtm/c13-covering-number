import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source33
namespace C13.Global.FastDual33_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,10]
def points : Finset C13.Point := {1,6,7,10}
def columns : List Code := [829,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1639,1646,1654,1693,1709,1721,1870,1882,1894,1906,1933,1945,1957,1969,2173,2238,2365,2397,2413,2425,2455,2462,2486,2621,2653,2669,2677,2731,2734,2746,2845,2861,2869,2873,2876,2893,2901,2905,2917,2921,2929,2951,2955,2958,2963,2966,2970,2979,2982,2986,2994,3011,3127,3131,3229,3245,3277,3292,3308,3355,3379,3418,3469,3493,3532,3623,3635,3686,3725,3737,3788]
def rows : List LinearRow := [⟨.covers 135,1,2⟩,⟨.covers 1031,1,2⟩,⟨.covers 75,1,9⟩,⟨.covers 139,1,2⟩,⟨.covers 77,1,5⟩,⟨.covers 141,1,1⟩,⟨.covers 149,1,3⟩,⟨.covers 101,1,5⟩,⟨.covers 197,1,12⟩,⟨.covers 89,1,5⟩,⟨.covers 169,1,2⟩,⟨.covers 297,1,2⟩,⟨.covers 1793,1,3⟩,⟨.covers 78,1,2⟩,⟨.covers 142,1,3⟩,⟨.covers 86,1,9⟩,⟨.covers 166,1,1⟩,⟨.covers 198,1,3⟩,⟨.covers 1286,1,2⟩,⟨.covers 154,1,2⟩,⟨.covers 554,1,2⟩,⟨.covers 202,1,7⟩,⟨.covers 1546,1,9⟩,⟨.covers 210,1,18⟩,⟨.covers 226,1,18⟩,⟨.covers 2818,1,1⟩,⟨.covers 3330,1,2⟩,⟨.covers 212,1,18⟩,⟨.covers 596,1,2⟩,⟨.covers 404,1,1⟩,⟨.covers 2580,1,2⟩,⟨.covers 228,1,7⟩,⟨.covers 420,1,1⟩,⟨.covers 1560,1,2⟩,⟨.covers 360,1,2⟩,⟨.covers 2384,1,5⟩,⟨.covers 1616,1,2⟩,⟨.covers 1424,1,1⟩,⟨.covers 2704,1,2⟩,⟨.covers 3600,1,2⟩,⟨.covers 1376,1,11⟩,⟨.covers 2656,1,5⟩,⟨.covers 3168,1,9⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,2⟩,⟨.covers 3232,1,2⟩,⟨.covers 2496,1,11⟩,⟨.covers 1728,1,18⟩,⟨.covers 2880,1,5⟩,⟨.covers 3392,1,7⟩,⟨.incident 6,8,-11⟩,⟨.incident 7,8,-5⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source33.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source33.rootCodes link33 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual33_008
namespace C13.Global.FastDual33_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,11]
def points : Finset C13.Point := {1,6,7,11}
def columns : List Code := [829,967,971,979,995,1150,1213,1341,1371,1374,1402,1437,1453,1461,1597,1639,1646,1654,1693,1709,1721,1821,1837,1845,1849,1852,1863,1867,1870,1875,1878,1882,1891,1894,1898,1906,1933,1941,1945,1957,1961,1969,1987,2173,2238,2397,2413,2425,2455,2462,2486,2653,2669,2677,2731,2734,2746,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3165,3181,3277,3292,3308,3351,3379,3405,3433,3478,3532,3627,3635,3661,3669,3754,3788,3851,3859,3913,3921,3978,3986,4040,4048]
def rows : List LinearRow := [⟨.covers 163,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 1728,1,1⟩,⟨.incident 7,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source33.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source33.rootCodes link33 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual33_009
namespace C13.Global.FastDual33_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,9,10]
def points : Finset C13.Point := {1,6,9,10}
def columns : List Code := [445,475,701,743,829,925,953,956,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1465,1498,1639,1646,1654,1693,1721,1766,1894,1945,2173,2231,2235,2237,2238,2269,2285,2365,2397,2413,2425,2455,2459,2461,2462,2477,2483,2485,2486,2489,2490,2492,2509,2521,2537,2621,2653,2677,2717,2731,2734,2745,2746,2748,2773,2845,2876,2901,2955,2969,2986,3000,3011,3025,3127,3131,3229,3245,3251,3253,3257,3277,3292,3308,3355,3379,3418,3469,3481,3493,3505,3532,3544,3686,3737]
def rows : List LinearRow := [⟨.covers 263,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 1793,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 1328,1,1⟩,⟨.covers 1584,1,1⟩,⟨.covers 848,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source33.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source33.rootCodes link33 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual33_010
namespace C13.Global.FastDual33_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,9,11]
def points : Finset C13.Point := {1,6,9,11}
def columns : List Code := [445,475,701,743,829,925,953,956,967,971,979,995,1150,1213,1341,1371,1374,1402,1437,1453,1461,1465,1468,1498,1597,1639,1646,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2173,2231,2235,2238,2269,2285,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2653,2677,2731,2734,2746,2773,2901,2986,3127,3131,3165,3181,3251,3254,3258,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 2055,1,5⟩,⟨.covers 75,1,1⟩,⟨.covers 523,1,8⟩,⟨.covers 1035,1,5⟩,⟨.covers 147,1,2⟩,⟨.covers 1539,1,13⟩,⟨.covers 2563,1,9⟩,⟨.covers 77,1,2⟩,⟨.covers 525,1,4⟩,⟨.covers 201,1,1⟩,⟨.covers 777,1,4⟩,⟨.covers 3081,1,3⟩,⟨.covers 1169,1,4⟩,⟨.covers 2337,1,1⟩,⟨.covers 3105,1,1⟩,⟨.covers 2817,1,9⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,5⟩,⟨.covers 270,1,6⟩,⟨.covers 198,1,13⟩,⟨.covers 2566,1,7⟩,⟨.covers 3078,1,3⟩,⟨.covers 106,1,6⟩,⟨.covers 1546,1,4⟩,⟨.covers 210,1,2⟩,⟨.covers 2818,1,16⟩,⟨.covers 3586,1,13⟩,⟨.covers 300,1,4⟩,⟨.covers 2316,1,1⟩,⟨.covers 1548,1,4⟩,⟨.covers 2572,1,9⟩,⟨.covers 2436,1,2⟩,⟨.covers 3204,1,1⟩,⟨.covers 232,1,4⟩,⟨.covers 688,1,4⟩,⟨.covers 2352,1,6⟩,⟨.covers 1584,1,4⟩,⟨.covers 2608,1,12⟩,⟨.covers 1232,1,3⟩,⟨.covers 848,1,5⟩,⟨.covers 1616,1,9⟩,⟨.covers 912,1,4⟩,⟨.covers 3216,1,2⟩,⟨.covers 864,1,13⟩,⟨.covers 2656,1,2⟩,⟨.covers 3168,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2752,1,14⟩,⟨.incident 1,8,-2⟩,⟨.incident 9,8,-7⟩,⟨.incident 11,8,-3⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source33.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source33.rootCodes link33 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual33_011
namespace C13.Global.FastDual33_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,10,11]
def points : Finset C13.Point := {1,6,10,11}
def columns : List Code := [445,475,701,743,829,925,941,949,953,956,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1465,1498,1639,1646,1654,1693,1709,1717,1721,1766,1870,1882,1894,1906,1933,1945,1957,1969,2173,2231,2235,2238,2269,2285,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2653,2669,2677,2731,2734,2739,2742,2746,2765,2773,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3251,3277,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 263,1,6⟩,⟨.covers 75,1,1⟩,⟨.covers 523,1,5⟩,⟨.covers 1539,1,9⟩,⟨.covers 77,1,2⟩,⟨.covers 1037,1,4⟩,⟨.covers 293,1,4⟩,⟨.covers 2309,1,1⟩,⟨.covers 1541,1,4⟩,⟨.covers 3077,1,9⟩,⟨.covers 89,1,1⟩,⟨.covers 1289,1,4⟩,⟨.covers 2569,1,3⟩,⟨.covers 3329,1,16⟩,⟨.covers 3585,1,7⟩,⟨.covers 142,1,5⟩,⟨.covers 1286,1,13⟩,⟨.covers 2566,1,3⟩,⟨.covers 3078,1,7⟩,⟨.covers 154,1,2⟩,⟨.covers 106,1,13⟩,⟨.covers 3082,1,16⟩,⟨.covers 210,1,2⟩,⟨.covers 226,1,6⟩,⟨.covers 2324,1,2⟩,⟨.covers 2580,1,1⟩,⟨.covers 664,1,4⟩,⟨.covers 2344,1,1⟩,⟨.covers 2600,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 3336,1,9⟩,⟨.covers 3592,1,11⟩,⟨.covers 2160,1,4⟩,⟨.covers 1200,1,4⟩,⟨.covers 720,1,3⟩,⟨.covers 2384,1,1⟩,⟨.covers 1616,1,13⟩,⟨.covers 3152,1,14⟩,⟨.covers 1424,1,4⟩,⟨.covers 2704,1,2⟩,⟨.covers 2656,1,1⟩,⟨.covers 3168,1,14⟩,⟨.covers 2464,1,6⟩,⟨.covers 1696,1,4⟩,⟨.covers 1472,1,5⟩,⟨.covers 1728,1,4⟩,⟨.incident 1,8,-2⟩,⟨.incident 10,8,-7⟩,⟨.incident 11,8,-3⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source33.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source33.rootCodes link33 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual33_012
namespace C13.Global.FastDual33_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,9,10]
def points : Finset C13.Point := {1,7,9,10}
def columns : List Code := [381,471,637,747,829,861,885,892,967,971,979,995,1143,1147,1150,1213,1245,1261,1371,1374,1395,1398,1402,1437,1453,1461,1485,1509,1639,1646,1654,1693,1721,1753,1894,1945,2173,2238,2365,2397,2413,2421,2425,2428,2455,2462,2486,2518,2621,2653,2677,2684,2731,2734,2746,2794,2845,2876,2901,2932,2955,2986,3011,3042,3127,3131,3187,3190,3194,3229,3245,3277,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 519,1,6⟩,⟨.covers 2055,1,5⟩,⟨.covers 75,1,1⟩,⟨.covers 1035,1,4⟩,⟨.covers 83,1,1⟩,⟨.covers 2563,1,13⟩,⟨.covers 141,1,1⟩,⟨.covers 525,1,4⟩,⟨.covers 197,1,2⟩,⟨.covers 773,1,4⟩,⟨.covers 1541,1,10⟩,⟨.covers 3077,1,3⟩,⟨.covers 2129,1,4⟩,⟨.covers 1313,1,1⟩,⟨.covers 3105,1,1⟩,⟨.covers 1793,1,8⟩,⟨.covers 3585,1,15⟩,⟨.covers 270,1,5⟩,⟨.covers 166,1,5⟩,⟨.covers 2566,1,4⟩,⟨.covers 202,1,12⟩,⟨.covers 1546,1,16⟩,⟨.covers 3082,1,3⟩,⟨.covers 210,1,1⟩,⟨.covers 1794,1,16⟩,⟨.covers 3586,1,12⟩,⟨.covers 300,1,4⟩,⟨.covers 1292,1,1⟩,⟨.covers 2572,1,4⟩,⟨.covers 228,1,4⟩,⟨.covers 2248,1,1⟩,⟨.covers 1352,1,2⟩,⟨.covers 3336,1,1⟩,⟨.covers 624,1,4⟩,⟨.covers 688,1,9⟩,⟨.covers 1328,1,6⟩,⟨.covers 2608,1,4⟩,⟨.covers 2256,1,4⟩,⟨.covers 848,1,4⟩,⟨.covers 1616,1,12⟩,⟨.covers 3152,1,2⟩,⟨.covers 912,1,6⟩,⟨.covers 928,1,13⟩,⟨.covers 1696,1,6⟩,⟨.covers 3232,1,2⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,3⟩,⟨.covers 3456,1,1⟩,⟨.incident 1,8,-1⟩,⟨.incident 9,8,-8⟩,⟨.incident 10,8,-3⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source33.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source33.rootCodes link33 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual33_013
namespace C13.Global.FastDual33_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,9,11]
def points : Finset C13.Point := {1,7,9,11}
def columns : List Code := [381,471,637,747,829,861,885,892,967,971,979,995,1143,1147,1149,1150,1213,1245,1261,1341,1367,1371,1373,1374,1389,1395,1397,1398,1401,1402,1404,1437,1453,1461,1485,1493,1509,1597,1629,1639,1646,1653,1654,1660,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2173,2238,2397,2413,2421,2425,2455,2462,2486,2518,2653,2677,2731,2734,2746,2794,2901,2986,3127,3131,3165,3181,3187,3189,3193,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 519,1,3⟩,⟨.covers 2055,1,2⟩,⟨.covers 267,1,10⟩,⟨.covers 1035,1,1⟩,⟨.covers 2059,1,4⟩,⟨.covers 147,1,9⟩,⟨.covers 99,1,7⟩,⟨.covers 2563,1,6⟩,⟨.covers 141,1,1⟩,⟨.covers 525,1,6⟩,⟨.covers 2061,1,4⟩,⟨.covers 297,1,2⟩,⟨.covers 2569,1,1⟩,⟨.covers 3081,1,6⟩,⟨.covers 2337,1,2⟩,⟨.covers 2817,1,11⟩,⟨.covers 3585,1,11⟩,⟨.covers 78,1,7⟩,⟨.covers 270,1,4⟩,⟨.covers 1062,1,1⟩,⟨.covers 198,1,2⟩,⟨.covers 774,1,6⟩,⟨.covers 2566,1,11⟩,⟨.covers 3078,1,8⟩,⟨.covers 154,1,6⟩,⟨.covers 202,1,1⟩,⟨.covers 114,1,3⟩,⟨.covers 178,1,3⟩,⟨.covers 226,1,2⟩,⟨.covers 1794,1,2⟩,⟨.covers 2818,1,11⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,11⟩,⟨.covers 156,1,1⟩,⟨.covers 300,1,3⟩,⟨.covers 1548,1,3⟩,⟨.covers 228,1,10⟩,⟨.covers 420,1,1⟩,⟨.covers 216,1,9⟩,⟨.covers 1800,1,2⟩,⟨.covers 3336,1,1⟩,⟨.covers 624,1,5⟩,⟨.covers 1200,1,9⟩,⟨.covers 1328,1,1⟩,⟨.covers 2352,1,8⟩,⟨.covers 1584,1,2⟩,⟨.covers 720,1,2⟩,⟨.covers 2704,1,3⟩,⟨.covers 3216,1,1⟩,⟨.covers 864,1,3⟩,⟨.covers 2656,1,6⟩,⟨.covers 3168,1,1⟩,⟨.covers 2496,1,9⟩,⟨.covers 2752,1,3⟩,⟨.covers 1920,1,9⟩,⟨.covers 3456,1,1⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source33.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source33.rootCodes link33 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual33_014
namespace C13.Global.FastDual33_015
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,10,11]
def points : Finset C13.Point := {1,7,10,11}
def columns : List Code := [381,471,637,747,829,861,877,885,889,892,967,971,979,995,1143,1147,1150,1213,1245,1261,1371,1374,1395,1398,1402,1437,1453,1461,1485,1509,1639,1646,1651,1654,1658,1693,1709,1721,1741,1753,1870,1882,1894,1906,1933,1945,1957,1969,2173,2238,2397,2413,2421,2425,2455,2462,2486,2518,2653,2669,2677,2681,2731,2734,2746,2794,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3187,3277,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 519,1,4⟩,⟨.covers 2055,1,6⟩,⟨.covers 267,1,5⟩,⟨.covers 2563,1,9⟩,⟨.covers 141,1,1⟩,⟨.covers 2061,1,4⟩,⟨.covers 149,1,2⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,3⟩,⟨.covers 3077,1,10⟩,⟨.covers 297,1,4⟩,⟨.covers 1289,1,1⟩,⟨.covers 2569,1,4⟩,⟨.covers 1793,1,1⟩,⟨.covers 3329,1,16⟩,⟨.covers 3585,1,7⟩,⟨.covers 78,1,5⟩,⟨.covers 142,1,1⟩,⟨.covers 86,1,2⟩,⟨.covers 550,1,1⟩,⟨.covers 2566,1,11⟩,⟨.covers 154,1,9⟩,⟨.covers 282,1,2⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,2⟩,⟨.covers 3082,1,16⟩,⟨.covers 226,1,5⟩,⟨.covers 180,1,1⟩,⟨.covers 596,1,4⟩,⟨.covers 420,1,1⟩,⟨.covers 184,1,2⟩,⟨.covers 792,1,1⟩,⟨.covers 1560,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3336,1,9⟩,⟨.covers 3592,1,11⟩,⟨.covers 2160,1,4⟩,⟨.covers 1200,1,1⟩,⟨.covers 720,1,5⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,2⟩,⟨.covers 3152,1,12⟩,⟨.covers 1424,1,3⟩,⟨.covers 2704,1,2⟩,⟨.covers 3216,1,3⟩,⟨.covers 1376,1,6⟩,⟨.covers 2656,1,4⟩,⟨.covers 2464,1,11⟩,⟨.covers 1696,1,3⟩,⟨.covers 3232,1,15⟩,⟨.covers 2496,1,7⟩,⟨.covers 2752,1,4⟩,⟨.incident 1,8,-1⟩,⟨.incident 10,8,-3⟩,⟨.incident 11,8,-8⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source33.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source33.rootCodes link33 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual33_015
