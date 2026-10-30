import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source22
namespace C13.Global.FastDual22_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,9]
def points : Finset C13.Point := {1,6,7,9}
def columns : List Code := [829,967,971,979,995,1150,1213,1341,1371,1374,1402,1437,1453,1461,1597,1639,1646,1654,1693,1721,1821,1852,1863,1894,1945,1987,2173,2238,2365,2397,2413,2425,2455,2462,2486,2621,2653,2677,2731,2734,2746,2845,2876,2901,2955,2986,3011,3127,3131,3133,3134,3165,3181,3196,3229,3245,3260,3277,3292,3308,3351,3355,3357,3358,3373,3379,3381,3382,3385,3386,3388,3405,3417,3418,3420,3433,3436,3448,3469,3477,3478,3484,3493,3500,3508,3532,3613,3630,3644,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 2384,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 1824,1,1⟩,⟨.covers 2848,1,1⟩,⟨.covers 2752,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_008
namespace C13.Global.FastDual22_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,11]
def points : Finset C13.Point := {1,6,7,11}
def columns : List Code := [829,967,971,979,995,1150,1213,1341,1371,1374,1402,1437,1453,1461,1597,1639,1646,1654,1693,1709,1721,1821,1837,1845,1849,1852,1863,1867,1870,1875,1878,1882,1891,1894,1898,1906,1933,1941,1945,1957,1961,1969,1987,2173,2238,2397,2413,2425,2455,2462,2486,2653,2669,2677,2731,2734,2746,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3165,3181,3277,3292,3308,3351,3379,3405,3433,3478,3532,3627,3635,3661,3669,3754,3788]
def rows : List LinearRow := [⟨.covers 2059,1,8⟩,⟨.covers 147,1,11⟩,⟨.covers 163,1,3⟩,⟨.covers 77,1,2⟩,⟨.covers 141,1,3⟩,⟨.covers 149,1,3⟩,⟨.covers 101,1,4⟩,⟨.covers 293,1,2⟩,⟨.covers 197,1,11⟩,⟨.covers 89,1,4⟩,⟨.covers 537,1,2⟩,⟨.covers 169,1,3⟩,⟨.covers 78,1,3⟩,⟨.covers 86,1,1⟩,⟨.covers 166,1,15⟩,⟨.covers 198,1,1⟩,⟨.covers 3078,1,8⟩,⟨.covers 282,1,2⟩,⟨.covers 106,1,1⟩,⟨.covers 202,1,12⟩,⟨.covers 2314,1,13⟩,⟨.covers 114,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,9⟩,⟨.covers 1794,1,2⟩,⟨.covers 212,1,17⟩,⟨.covers 596,1,2⟩,⟨.covers 228,1,17⟩,⟨.covers 612,1,2⟩,⟨.covers 1316,1,2⟩,⟨.covers 1560,1,2⟩,⟨.covers 360,1,2⟩,⟨.covers 2824,1,2⟩,⟨.covers 2384,1,4⟩,⟨.covers 1424,1,3⟩,⟨.covers 2704,1,15⟩,⟨.covers 3600,1,8⟩,⟨.covers 2656,1,2⟩,⟨.covers 1696,1,3⟩,⟨.covers 3360,1,8⟩,⟨.covers 1472,1,1⟩,⟨.covers 2496,1,16⟩,⟨.covers 1728,1,6⟩,⟨.covers 2880,1,4⟩,⟨.covers 1920,1,3⟩,⟨.covers 3712,1,11⟩,⟨.incident 6,8,-2⟩,⟨.incident 7,8,-6⟩,⟨.incident 11,8,-5⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_009
namespace C13.Global.FastDual22_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,8,9]
def points : Finset C13.Point := {1,6,8,9}
def columns : List Code := [254,445,475,506,701,743,758,829,956,967,971,979,995,1010,1150,1213,1341,1371,1374,1402,1453,1461,1468,1498,1597,1639,1646,1654,1693,1721,1724,1766,1852,1987,2173,2231,2235,2237,2238,2269,2285,2300,2365,2413,2425,2455,2462,2477,2485,2486,2492,2537,2552,2621,2653,2677,2717,2731,2734,2745,2746,2748,2773,2804,2876,3011,3056,3127,3131,3133,3134,3165,3181,3196,3229,3245,3251,3253,3254,3257,3258,3260,3277,3292,3308,3358,3373,3388,3418,3433,3448,3478,3493,3508,3613,3630,3644,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 99,1,2⟩,⟨.covers 2563,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 774,1,2⟩,⟨.covers 2566,1,1⟩,⟨.covers 778,1,2⟩,⟨.covers 1794,1,2⟩,⟨.covers 2818,1,1⟩,⟨.covers 1800,1,2⟩,⟨.covers 2824,1,2⟩,⟨.covers 848,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 3712,1,1⟩,⟨.incident 9,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_010
namespace C13.Global.FastDual22_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,8,11]
def points : Finset C13.Point := {1,6,8,11}
def columns : List Code := [254,445,475,506,701,743,758,829,941,949,956,967,971,979,995,1010,1150,1213,1341,1371,1374,1402,1453,1461,1468,1498,1597,1639,1646,1654,1693,1709,1717,1721,1724,1766,1837,1852,1867,1882,1957,1972,1987,2002,2173,2231,2235,2238,2269,2285,2300,2413,2425,2455,2462,2486,2537,2552,2653,2669,2677,2731,2734,2739,2742,2746,2765,2773,2804,2921,2966,3056,3127,3131,3165,3181,3251,3254,3258,3277,3292,3308,3433,3478,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 263,1,16⟩,⟨.covers 1031,1,12⟩,⟨.covers 2059,1,8⟩,⟨.covers 83,1,20⟩,⟨.covers 99,1,8⟩,⟨.covers 163,1,6⟩,⟨.covers 2307,1,4⟩,⟨.covers 2563,1,5⟩,⟨.covers 77,1,3⟩,⟨.covers 269,1,3⟩,⟨.covers 197,1,3⟩,⟨.covers 2097,1,2⟩,⟨.covers 2129,1,1⟩,⟨.covers 2577,1,3⟩,⟨.covers 417,1,3⟩,⟨.covers 270,1,16⟩,⟨.covers 526,1,19⟩,⟨.covers 1038,1,1⟩,⟨.covers 86,1,3⟩,⟨.covers 778,1,20⟩,⟨.covers 2314,1,4⟩,⟨.covers 3082,1,4⟩,⟨.covers 114,1,14⟩,⟨.covers 1074,1,2⟩,⟨.covers 2098,1,4⟩,⟨.covers 226,1,3⟩,⟨.covers 2818,1,20⟩,⟨.covers 3330,1,20⟩,⟨.covers 3586,1,4⟩,⟨.covers 120,1,1⟩,⟨.covers 664,1,7⟩,⟨.covers 2696,1,1⟩,⟨.covers 3208,1,1⟩,⟨.covers 2824,1,7⟩,⟨.covers 3336,1,7⟩,⟨.covers 624,1,1⟩,⟨.covers 1328,1,3⟩,⟨.covers 2352,1,3⟩,⟨.covers 3152,1,3⟩,⟨.covers 3232,1,6⟩,⟨.covers 1824,1,3⟩,⟨.covers 1472,1,20⟩,⟨.covers 2496,1,4⟩,⟨.covers 3712,1,4⟩,⟨.incident 1,8,-13⟩,⟨.incident 11,8,-1⟩]
def bound : Int := 8

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_011
namespace C13.Global.FastDual22_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,9,11]
def points : Finset C13.Point := {1,6,9,11}
def columns : List Code := [254,445,475,506,701,743,758,829,925,953,956,967,971,979,995,1010,1150,1213,1341,1371,1374,1402,1437,1453,1461,1465,1468,1498,1597,1639,1646,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2173,2231,2235,2238,2269,2285,2300,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2552,2653,2677,2731,2734,2746,2773,2804,2901,2986,3056,3127,3131,3165,3181,3251,3254,3258,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 75,1,1⟩,⟨.covers 523,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 99,1,2⟩,⟨.covers 2563,1,1⟩,⟨.covers 270,1,2⟩,⟨.covers 774,1,2⟩,⟨.covers 2566,1,2⟩,⟨.covers 3078,1,1⟩,⟨.covers 1546,1,2⟩,⟨.covers 114,1,2⟩,⟨.covers 2098,1,1⟩,⟨.covers 2818,1,2⟩,⟨.covers 3330,1,1⟩,⟨.covers 1728,1,2⟩,⟨.incident 1,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_012
namespace C13.Global.FastDual22_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,8,9]
def points : Finset C13.Point := {1,7,8,9}
def columns : List Code := [381,471,637,747,829,892,967,971,979,995,1143,1147,1149,1150,1213,1245,1261,1341,1371,1374,1389,1401,1402,1404,1453,1461,1509,1597,1629,1639,1646,1653,1654,1660,1693,1721,1753,1852,1987,2173,2238,2365,2413,2425,2428,2455,2462,2486,2518,2621,2653,2677,2684,2731,2734,2746,2794,2876,3011,3127,3131,3133,3134,3165,3181,3187,3189,3190,3193,3194,3196,3229,3245,3260,3277,3292,3308,3358,3373,3388,3418,3433,3448,3478,3493,3508,3613,3630,3644,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 519,1,1⟩,⟨.covers 1031,1,9⟩,⟨.covers 2055,1,2⟩,⟨.covers 267,1,1⟩,⟨.covers 1035,1,7⟩,⟨.covers 2059,1,4⟩,⟨.covers 269,1,5⟩,⟨.covers 525,1,1⟩,⟨.covers 2061,1,2⟩,⟨.covers 149,1,9⟩,⟨.covers 169,1,2⟩,⟨.covers 1289,1,3⟩,⟨.covers 2569,1,5⟩,⟨.covers 1553,1,1⟩,⟨.covers 2577,1,2⟩,⟨.covers 2145,1,3⟩,⟨.covers 1313,1,1⟩,⟨.covers 78,1,7⟩,⟨.covers 270,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 774,1,9⟩,⟨.covers 1286,1,3⟩,⟨.covers 2566,1,9⟩,⟨.covers 154,1,10⟩,⟨.covers 106,1,3⟩,⟨.covers 778,1,10⟩,⟨.covers 114,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 1794,1,11⟩,⟨.covers 2818,1,11⟩,⟨.covers 3330,1,7⟩,⟨.covers 228,1,3⟩,⟨.covers 216,1,2⟩,⟨.covers 232,1,6⟩,⟨.covers 1800,1,11⟩,⟨.covers 2824,1,11⟩,⟨.covers 368,1,5⟩,⟨.covers 624,1,4⟩,⟨.covers 720,1,3⟩,⟨.covers 2256,1,9⟩,⟨.covers 848,1,1⟩,⟨.covers 2384,1,2⟩,⟨.covers 1616,1,5⟩,⟨.covers 912,1,7⟩,⟨.covers 1424,1,1⟩,⟨.covers 480,1,5⟩,⟨.covers 2272,1,2⟩,⟨.covers 1376,1,1⟩,⟨.covers 928,1,5⟩,⟨.covers 2464,1,10⟩,⟨.covers 1696,1,8⟩,⟨.covers 3392,1,2⟩,⟨.covers 3648,1,1⟩,⟨.covers 3712,1,3⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_013
namespace C13.Global.FastDual22_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,8,11]
def points : Finset C13.Point := {1,7,8,11}
def columns : List Code := [381,471,637,747,829,877,889,892,967,971,979,995,1143,1147,1149,1150,1213,1245,1261,1341,1371,1374,1389,1401,1402,1404,1453,1461,1509,1597,1629,1639,1643,1645,1646,1651,1653,1654,1657,1658,1660,1693,1709,1721,1741,1753,1769,1837,1852,1867,1882,1897,1912,1957,1987,2017,2173,2238,2413,2425,2455,2462,2486,2518,2653,2669,2677,2681,2731,2734,2746,2794,2921,2966,3127,3131,3165,3181,3187,3189,3193,3277,3292,3308,3433,3478,3627,3635,3661,3669,3689,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 519,1,1⟩,⟨.covers 2055,1,1⟩,⟨.covers 267,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 1920,1,1⟩,⟨.covers 3712,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_014
namespace C13.Global.FastDual22_015
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,9,11]
def points : Finset C13.Point := {1,7,9,11}
def columns : List Code := [381,471,637,747,829,861,885,892,967,971,979,995,1143,1147,1149,1150,1213,1245,1261,1341,1367,1371,1373,1374,1389,1395,1397,1398,1401,1402,1404,1437,1453,1461,1485,1493,1509,1597,1629,1639,1646,1653,1654,1660,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2173,2238,2397,2413,2421,2425,2455,2462,2486,2518,2653,2677,2731,2734,2746,2794,2901,2986,3127,3131,3165,3181,3187,3189,3193,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 519,1,5⟩,⟨.covers 267,1,10⟩,⟨.covers 1035,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 147,1,11⟩,⟨.covers 99,1,3⟩,⟨.covers 1059,1,1⟩,⟨.covers 2563,1,10⟩,⟨.covers 141,1,4⟩,⟨.covers 525,1,6⟩,⟨.covers 2061,1,5⟩,⟨.covers 297,1,2⟩,⟨.covers 777,1,1⟩,⟨.covers 3081,1,2⟩,⟨.covers 78,1,4⟩,⟨.covers 270,1,7⟩,⟨.covers 1062,1,1⟩,⟨.covers 774,1,5⟩,⟨.covers 2566,1,11⟩,⟨.covers 3078,1,8⟩,⟨.covers 1546,1,5⟩,⟨.covers 3082,1,6⟩,⟨.covers 114,1,3⟩,⟨.covers 2818,1,11⟩,⟨.covers 3330,1,2⟩,⟨.covers 2316,1,4⟩,⟨.covers 1548,1,1⟩,⟨.covers 228,1,7⟩,⟨.covers 120,1,2⟩,⟨.covers 184,1,7⟩,⟨.covers 312,1,2⟩,⟨.covers 216,1,7⟩,⟨.covers 1800,1,3⟩,⟨.covers 624,1,3⟩,⟨.covers 2160,1,3⟩,⟨.covers 432,1,11⟩,⟨.covers 1584,1,4⟩,⟨.covers 2256,1,4⟩,⟨.covers 2704,1,4⟩,⟨.covers 2832,1,11⟩,⟨.covers 3600,1,11⟩,⟨.covers 480,1,4⟩,⟨.covers 2272,1,4⟩,⟨.covers 864,1,4⟩,⟨.covers 2656,1,5⟩,⟨.covers 1824,1,1⟩,⟨.covers 3360,1,7⟩,⟨.covers 2496,1,7⟩,⟨.covers 1728,1,4⟩,⟨.covers 2752,1,2⟩,⟨.covers 1920,1,7⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_015
