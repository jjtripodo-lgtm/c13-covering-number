import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source15
namespace C13.Global.FastDual15_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,9,10]
def points : Finset C13.Point := {1,6,9,10}
def columns : List Code := [445,475,701,743,829,925,953,956,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1465,1498,1639,1646,1654,1693,1721,1766,1894,1945,2173,2231,2235,2237,2238,2269,2285,2365,2397,2413,2425,2455,2459,2461,2462,2477,2483,2485,2486,2489,2490,2492,2509,2521,2537,2621,2653,2677,2717,2731,2734,2745,2746,2748,2773,2845,2876,2901,2955,2969,2986,3000,3011,3025,3127,3131,3229,3245,3251,3253,3257,3277,3292,3308,3355,3379,3418,3469,3481,3493,3505,3532,3544,3686,3737]
def rows : List LinearRow := [⟨.covers 263,1,12⟩,⟨.covers 523,1,3⟩,⟨.covers 1035,1,6⟩,⟨.covers 83,1,6⟩,⟨.covers 163,1,9⟩,⟨.covers 1539,1,12⟩,⟨.covers 77,1,1⟩,⟨.covers 1037,1,7⟩,⟨.covers 533,1,5⟩,⟨.covers 293,1,2⟩,⟨.covers 142,1,9⟩,⟨.covers 270,1,3⟩,⟨.covers 1286,1,3⟩,⟨.covers 3078,1,12⟩,⟨.covers 778,1,9⟩,⟨.covers 1546,1,12⟩,⟨.covers 3082,1,6⟩,⟨.covers 178,1,3⟩,⟨.covers 210,1,6⟩,⟨.covers 1794,1,8⟩,⟨.covers 92,1,3⟩,⟨.covers 1292,1,2⟩,⟨.covers 2572,1,2⟩,⟨.covers 308,1,5⟩,⟨.covers 2244,1,1⟩,⟨.covers 3204,1,2⟩,⟨.covers 232,1,9⟩,⟨.covers 1800,1,12⟩,⟨.covers 3592,1,12⟩,⟨.covers 368,1,7⟩,⟨.covers 2160,1,4⟩,⟨.covers 688,1,7⟩,⟨.covers 1328,1,4⟩,⟨.covers 2608,1,2⟩,⟨.covers 1616,1,12⟩,⟨.covers 3152,1,6⟩,⟨.covers 480,1,3⟩,⟨.covers 1696,1,5⟩,⟨.covers 2848,1,3⟩,⟨.covers 3360,1,7⟩,⟨.covers 1472,1,6⟩,⟨.covers 1728,1,7⟩,⟨.covers 2752,1,5⟩,⟨.covers 2880,1,6⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source15.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source15.rootCodes link15 points rows bound = true := by decide +kernel

end C13.Global.FastDual15_008
namespace C13.Global.FastDual15_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,9,11]
def points : Finset C13.Point := {1,6,9,11}
def columns : List Code := [445,475,701,743,829,925,953,956,967,971,979,995,1150,1213,1341,1371,1374,1402,1437,1453,1461,1465,1468,1498,1597,1639,1646,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2173,2231,2235,2238,2269,2285,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2653,2677,2731,2734,2746,2773,2901,2986,3127,3131,3165,3181,3251,3254,3258,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 1539,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 368,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 1232,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 2832,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 864,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 2496,1,1⟩,⟨.incident 11,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source15.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source15.rootCodes link15 points rows bound = true := by decide +kernel

end C13.Global.FastDual15_009
namespace C13.Global.FastDual15_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,10,11]
def points : Finset C13.Point := {1,6,10,11}
def columns : List Code := [445,475,701,743,829,925,941,949,953,956,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1465,1498,1639,1646,1654,1693,1709,1717,1721,1766,1870,1882,1894,1906,1933,1945,1957,1969,2173,2231,2235,2238,2269,2285,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2653,2669,2677,2731,2734,2739,2742,2746,2765,2773,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3251,3277,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 263,1,12⟩,⟨.covers 1031,1,2⟩,⟨.covers 75,1,2⟩,⟨.covers 523,1,10⟩,⟨.covers 1035,1,8⟩,⟨.covers 99,1,9⟩,⟨.covers 77,1,5⟩,⟨.covers 1037,1,4⟩,⟨.covers 293,1,2⟩,⟨.covers 1289,1,1⟩,⟨.covers 2569,1,3⟩,⟨.covers 3081,1,1⟩,⟨.covers 142,1,8⟩,⟨.covers 86,1,12⟩,⟨.covers 166,1,2⟩,⟨.covers 2566,1,2⟩,⟨.covers 3078,1,12⟩,⟨.covers 154,1,1⟩,⟨.covers 554,1,2⟩,⟨.covers 2314,1,3⟩,⟨.covers 1546,1,10⟩,⟨.covers 3082,1,5⟩,⟨.covers 178,1,3⟩,⟨.covers 210,1,9⟩,⟨.covers 3330,1,14⟩,⟨.covers 3586,1,14⟩,⟨.covers 540,1,1⟩,⟨.covers 308,1,1⟩,⟨.covers 788,1,3⟩,⟨.covers 2324,1,3⟩,⟨.covers 2580,1,1⟩,⟨.covers 664,1,2⟩,⟨.covers 2344,1,3⟩,⟨.covers 1800,1,2⟩,⟨.covers 2824,1,2⟩,⟨.covers 3336,1,10⟩,⟨.covers 3592,1,4⟩,⟨.covers 2160,1,5⟩,⟨.covers 1200,1,2⟩,⟨.covers 720,1,3⟩,⟨.covers 2384,1,2⟩,⟨.covers 3152,1,1⟩,⟨.covers 1424,1,2⟩,⟨.covers 2704,1,6⟩,⟨.covers 3216,1,9⟩,⟨.covers 480,1,2⟩,⟨.covers 1376,1,12⟩,⟨.covers 2656,1,2⟩,⟨.covers 3168,1,10⟩,⟨.covers 2464,1,5⟩,⟨.covers 1696,1,3⟩,⟨.covers 1728,1,6⟩,⟨.covers 2880,1,1⟩,⟨.incident 1,8,-4⟩,⟨.incident 11,8,-3⟩]
def bound : Int := 8

theorem column_mask : listMask columns = restrictMask universeMask Source15.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source15.rootCodes link15 points rows bound = true := by decide +kernel

end C13.Global.FastDual15_010
namespace C13.Global.FastDual15_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,7,8,9]
def points : Finset C13.Point := {6,7,8,9}
def columns : List Code := [127,191,223,239,319,351,367,379,415,431,439,463,575,607,623,631,671,687,699,719,799,815,829,830,847,911,967,971,979,995,1087,1119,1135,1150,1183,1199,1213,1231,1311,1327,1341,1342,1359,1371,1374,1387,1402,1423,1431,1447,1453,1461,1567,1583,1597,1598,1615,1623,1639,1646,1654,1679,1691,1693,1707,1721,1807,1852,1987,2111,2143,2159,2173,2207,2223,2238,2255,2335,2351,2365,2366,2383,2395,2411,2413,2425,2447,2455,2462,2471,2486,2591,2607,2621,2622,2639,2647,2653,2663,2677,2703,2715,2731,2734,2746,2831,2876,3011,3103,3119,3127,3131,3133,3134,3151,3165,3166,3181,3182,3196,3215,3229,3230,3245,3246,3260,3277,3278,3292,3308,3343,3358,3373,3388,3403,3418,3433,3448,3463,3478,3493,3508,3599,3613,3630,3644,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 1043,1,1⟩,⟨.covers 2083,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 464,1,2⟩,⟨.covers 1232,1,2⟩,⟨.covers 2384,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 1808,1,2⟩,⟨.covers 2832,1,2⟩,⟨.covers 480,1,2⟩,⟨.covers 1248,1,2⟩,⟨.covers 1376,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 1472,1,2⟩,⟨.covers 2496,1,2⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source15.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source15.rootCodes link15 points rows bound = true := by decide +kernel

end C13.Global.FastDual15_011
namespace C13.Global.FastDual15_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [8,9,10,11]
def points : Finset C13.Point := {8,9,10,11}
def columns : List Code := [127,191,223,239,247,251,253,254,319,351,367,379,381,382,415,431,439,445,446,463,471,475,478,487,491,493,499,501,502,505,506,508,575,607,623,631,637,638,671,687,699,701,702,719,727,731,733,743,747,750,755,757,758,761,762,764,799,815,829,830,847,892,911,956,967,971,979,995,1009,1010,1012,1016,1087,1119,1135,1143,1147,1150,1183,1199,1207,1211,1213,1231,1243,1245,1246,1255,1261,1262,1267,1269,1270,1273,1274,1276,1311,1327,1359,1371,1374,1402,1423,1447,1453,1461,1498,1509,1521,1522,1524,1528,1567,1583,1615,1639,1646,1654,1679,1691,1693,1721,1753,1766,1777,1778,1780,1784,1807,2032,2111,2143,2159,2167,2171,2173,2207,2223,2231,2235,2238,2255,2263,2269,2270,2283,2285,2286,2291,2293,2294,2297,2298,2300,2335,2351,2383,2411,2413,2425,2447,2455,2462,2486,2518,2537,2545,2546,2548,2552,2591,2607,2639,2647,2653,2677,2703,2731,2734,2746,2773,2794,2801,2802,2804,2808,2831,3056,3103,3119,3127,3131,3151,3187,3215,3251,3277,3278,3292,3308,3313,3314,3316,3320,3343,3568,3599,3824]
def rows : List LinearRow := [⟨.covers 1313,1,1⟩,⟨.covers 3105,1,1⟩,⟨.covers 1346,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 1604,1,1⟩,⟨.covers 3144,1,1⟩,⟨.covers 1672,1,1⟩,⟨.covers 1808,1,1⟩,⟨.covers 3344,1,1⟩,⟨.covers 3600,1,1⟩,⟨.incident 10,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source15.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source15.rootCodes link15 points rows bound = true := by decide +kernel

end C13.Global.FastDual15_012
