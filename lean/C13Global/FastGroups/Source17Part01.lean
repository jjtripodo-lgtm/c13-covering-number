import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source17
namespace C13.Global.FastDual17_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,8,10]
def points : Finset C13.Point := {1,3,8,10}
def columns : List Code := [247,251,253,254,381,471,499,501,502,505,506,508,701,743,755,757,758,761,762,764,829,889,892,949,956,967,979,982,995,997,1009,1010,1012,1016,1143,1245,1267,1269,1270,1273,1274,1276,1371,1374,1402,1461,1498,1509,1521,1522,1524,1528,1639,1651,1654,1693,1717,1721,1753,1756,1765,1766,1777,1778,1780,1784,1882,1957,2032,2231,2285,2291,2293,2294,2297,2298,2300,2413,2425,2428,2455,2485,2486,2515,2518,2533,2537,2545,2546,2548,2552,2677,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2773,2787,2789,2790,2793,2794,2796,2801,2802,2804,2808,2861,2876,2921,2936,2951,2966,2981,2996,3011,3026,3041,3056,3127,3187,3190,3251,3253,3277,3289,3292,3301,3308,3313,3314,3316,3320,3418,3493,3568,3623,3635,3686,3698,3725,3737,3749,3761,3788,3800,3812,3824]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 267,1,2⟩,⟨.covers 523,1,2⟩,⟨.covers 147,1,1⟩,⟨.covers 2307,1,1⟩,⟨.covers 1539,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 593,1,1⟩,⟨.covers 270,1,2⟩,⟨.covers 526,1,2⟩,⟨.covers 774,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 778,1,2⟩,⟨.covers 2314,1,2⟩,⟨.covers 156,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 2132,1,1⟩,⟨.covers 1796,1,2⟩,⟨.covers 3332,1,2⟩,⟨.covers 1424,1,1⟩,⟨.covers 2880,1,1⟩,⟨.covers 3648,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_008
namespace C13.Global.FastDual17_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,9,11]
def points : Finset C13.Point := {1,3,9,11}
def columns : List Code := [247,251,253,254,381,471,499,501,502,505,506,508,701,743,755,757,758,761,762,764,829,885,892,953,956,967,979,981,995,998,1009,1010,1012,1016,1143,1245,1267,1269,1270,1273,1274,1276,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1491,1493,1494,1497,1498,1500,1509,1521,1522,1524,1528,1639,1653,1654,1693,1721,1724,1749,1753,1763,1766,1777,1778,1780,1784,1821,1852,1863,1877,1894,1908,1945,1976,1987,2001,2018,2032,2231,2285,2291,2293,2294,2297,2298,2300,2413,2421,2425,2455,2483,2486,2517,2518,2537,2540,2545,2546,2548,2552,2677,2731,2734,2746,2773,2794,2801,2802,2804,2808,2901,2986,3056,3127,3187,3189,3251,3254,3277,3285,3292,3305,3308,3313,3314,3316,3320,3351,3379,3405,3413,3433,3441,3478,3506,3532,3540,3560,3568,3669,3754,3824]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 267,1,2⟩,⟨.covers 523,1,2⟩,⟨.covers 147,1,1⟩,⟨.covers 1539,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 417,1,1⟩,⟨.covers 270,1,2⟩,⟨.covers 526,1,2⟩,⟨.covers 3078,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 778,1,2⟩,⟨.covers 1546,1,2⟩,⟨.covers 156,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 1188,1,1⟩,⟨.covers 2820,1,2⟩,⟨.covers 3588,1,2⟩,⟨.covers 2608,1,1⟩,⟨.covers 1824,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_009
namespace C13.Global.FastDual17_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,8,9]
def points : Finset C13.Point := {1,6,8,9}
def columns : List Code := [445,475,701,743,829,956,967,971,979,995,1150,1213,1341,1371,1374,1402,1453,1461,1468,1498,1597,1639,1646,1654,1693,1721,1724,1766,1852,1987,2173,2231,2235,2237,2238,2269,2285,2365,2413,2425,2455,2462,2477,2485,2486,2492,2537,2621,2653,2677,2717,2731,2734,2745,2746,2748,2773,2876,3011,3127,3131,3133,3134,3165,3181,3196,3229,3245,3251,3253,3254,3257,3258,3260,3277,3292,3308,3358,3373,3388,3418,3433,3448,3478,3493,3508,3613,3630,3644,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 1031,1,3⟩,⟨.covers 2055,1,8⟩,⟨.covers 1035,1,3⟩,⟨.covers 2059,1,8⟩,⟨.covers 77,1,7⟩,⟨.covers 773,1,11⟩,⟨.covers 2309,1,3⟩,⟨.covers 1541,1,8⟩,⟨.covers 1289,1,8⟩,⟨.covers 2569,1,3⟩,⟨.covers 2129,1,1⟩,⟨.covers 1169,1,3⟩,⟨.covers 2145,1,1⟩,⟨.covers 1185,1,3⟩,⟨.covers 142,1,8⟩,⟨.covers 526,1,3⟩,⟨.covers 86,1,11⟩,⟨.covers 778,1,11⟩,⟨.covers 2314,1,3⟩,⟨.covers 1546,1,8⟩,⟨.covers 178,1,3⟩,⟨.covers 226,1,3⟩,⟨.covers 1794,1,11⟩,⟨.covers 2818,1,11⟩,⟨.covers 3330,1,8⟩,⟨.covers 1796,1,11⟩,⟨.covers 2820,1,11⟩,⟨.covers 216,1,3⟩,⟨.covers 232,1,3⟩,⟨.covers 368,1,9⟩,⟨.covers 432,1,5⟩,⟨.covers 688,1,5⟩,⟨.covers 1232,1,8⟩,⟨.covers 848,1,11⟩,⟨.covers 2704,1,3⟩,⟨.covers 480,1,4⟩,⟨.covers 1248,1,8⟩,⟨.covers 864,1,4⟩,⟨.covers 1376,1,2⟩,⟨.covers 2656,1,9⟩,⟨.covers 2464,1,3⟩,⟨.covers 3648,1,2⟩,⟨.covers 3456,1,3⟩,⟨.covers 3712,1,3⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_010
namespace C13.Global.FastDual17_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,8,11]
def points : Finset C13.Point := {1,6,8,11}
def columns : List Code := [445,475,701,743,829,941,949,956,967,971,979,995,1150,1213,1341,1371,1374,1402,1453,1461,1468,1498,1597,1639,1646,1654,1693,1709,1717,1721,1724,1766,1837,1852,1867,1882,1957,1972,1987,2002,2173,2231,2235,2238,2269,2285,2413,2425,2455,2462,2486,2537,2653,2669,2677,2731,2734,2739,2742,2746,2765,2773,2921,2966,3127,3131,3165,3181,3251,3254,3258,3277,3292,3308,3433,3478,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 1031,1,4⟩,⟨.covers 139,1,4⟩,⟨.covers 2059,1,3⟩,⟨.covers 1043,1,4⟩,⟨.covers 99,1,3⟩,⟨.covers 163,1,4⟩,⟨.covers 1283,1,5⟩,⟨.covers 2307,1,3⟩,⟨.covers 2563,1,2⟩,⟨.covers 77,1,2⟩,⟨.covers 141,1,1⟩,⟨.covers 269,1,2⟩,⟨.covers 1157,1,2⟩,⟨.covers 773,1,5⟩,⟨.covers 2309,1,10⟩,⟨.covers 3077,1,6⟩,⟨.covers 1161,1,3⟩,⟨.covers 593,1,4⟩,⟨.covers 526,1,8⟩,⟨.covers 86,1,3⟩,⟨.covers 774,1,2⟩,⟨.covers 202,1,1⟩,⟨.covers 650,1,1⟩,⟨.covers 778,1,4⟩,⟨.covers 2314,1,13⟩,⟨.covers 3082,1,6⟩,⟨.covers 114,1,1⟩,⟨.covers 178,1,2⟩,⟨.covers 2818,1,11⟩,⟨.covers 3330,1,13⟩,⟨.covers 3586,1,2⟩,⟨.covers 92,1,4⟩,⟨.covers 1292,1,1⟩,⟨.covers 2572,1,4⟩,⟨.covers 1796,1,1⟩,⟨.covers 3588,1,2⟩,⟨.covers 184,1,1⟩,⟨.covers 568,1,2⟩,⟨.covers 216,1,4⟩,⟨.covers 664,1,3⟩,⟨.covers 3208,1,1⟩,⟨.covers 2824,1,13⟩,⟨.covers 3336,1,11⟩,⟨.covers 624,1,4⟩,⟨.covers 432,1,2⟩,⟨.covers 1328,1,5⟩,⟨.covers 2608,1,6⟩,⟨.covers 2256,1,3⟩,⟨.covers 848,1,5⟩,⟨.covers 2384,1,13⟩,⟨.covers 3152,1,2⟩,⟨.covers 1248,1,8⟩,⟨.covers 1376,1,2⟩,⟨.covers 928,1,1⟩,⟨.covers 2464,1,10⟩,⟨.covers 3232,1,4⟩,⟨.covers 1472,1,4⟩,⟨.covers 2496,1,3⟩,⟨.covers 2752,1,7⟩,⟨.incident 11,8,-5⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_011
namespace C13.Global.FastDual17_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,9,10]
def points : Finset C13.Point := {1,6,9,10}
def columns : List Code := [445,475,701,743,829,925,953,956,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1465,1498,1639,1646,1654,1693,1721,1766,1894,1945,2173,2231,2235,2237,2238,2269,2285,2365,2397,2413,2425,2455,2459,2461,2462,2477,2483,2485,2486,2489,2490,2492,2509,2521,2537,2621,2653,2677,2717,2731,2734,2745,2746,2748,2773,2845,2876,2901,2955,2969,2986,3000,3011,3025,3127,3131,3229,3245,3251,3253,3257,3277,3292,3308,3355,3379,3418,3469,3481,3493,3505,3532,3544,3686,3737]
def rows : List LinearRow := [⟨.covers 263,1,7⟩,⟨.covers 1031,1,3⟩,⟨.covers 2055,1,4⟩,⟨.covers 75,1,11⟩,⟨.covers 163,1,4⟩,⟨.covers 2083,1,1⟩,⟨.covers 1539,1,4⟩,⟨.covers 2563,1,4⟩,⟨.covers 77,1,4⟩,⟨.covers 525,1,2⟩,⟨.covers 1037,1,4⟩,⟨.covers 293,1,2⟩,⟨.covers 773,1,4⟩,⟨.covers 1541,1,4⟩,⟨.covers 3077,1,2⟩,⟨.covers 142,1,7⟩,⟨.covers 270,1,4⟩,⟨.covers 526,1,1⟩,⟨.covers 2090,1,1⟩,⟨.covers 1546,1,10⟩,⟨.covers 3082,1,8⟩,⟨.covers 178,1,1⟩,⟨.covers 1794,1,11⟩,⟨.covers 2818,1,7⟩,⟨.covers 3330,1,3⟩,⟨.covers 3586,1,1⟩,⟨.covers 92,1,4⟩,⟨.covers 172,1,2⟩,⟨.covers 1292,1,2⟩,⟨.covers 308,1,2⟩,⟨.covers 2132,1,1⟩,⟨.covers 2244,1,1⟩,⟨.covers 2820,1,4⟩,⟨.covers 3332,1,2⟩,⟨.covers 232,1,4⟩,⟨.covers 1800,1,11⟩,⟨.covers 3592,1,11⟩,⟨.covers 368,1,9⟩,⟨.covers 2160,1,2⟩,⟨.covers 688,1,7⟩,⟨.covers 1200,1,4⟩,⟨.covers 1328,1,2⟩,⟨.covers 2608,1,2⟩,⟨.covers 720,1,9⟩,⟨.covers 1232,1,5⟩,⟨.covers 848,1,1⟩,⟨.covers 1616,1,11⟩,⟨.covers 480,1,7⟩,⟨.covers 2656,1,6⟩,⟨.covers 3168,1,4⟩,⟨.covers 2848,1,2⟩,⟨.covers 3360,1,4⟩,⟨.covers 1472,1,6⟩,⟨.covers 1728,1,11⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_012
namespace C13.Global.FastDual17_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,9,11]
def points : Finset C13.Point := {1,6,9,11}
def columns : List Code := [445,475,701,743,829,925,953,956,967,971,979,995,1150,1213,1341,1371,1374,1402,1437,1453,1461,1465,1468,1498,1597,1639,1646,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2173,2231,2235,2238,2269,2285,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2653,2677,2731,2734,2746,2773,2901,2986,3127,3131,3165,3181,3251,3254,3258,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 1539,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 368,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 1232,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 864,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 2496,1,1⟩,⟨.incident 11,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_013
namespace C13.Global.FastDual17_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,8,9]
def points : Finset C13.Point := {1,7,8,9}
def columns : List Code := [381,471,637,747,829,892,967,971,979,995,1143,1147,1149,1150,1213,1245,1261,1341,1371,1374,1389,1401,1402,1404,1453,1461,1509,1597,1629,1639,1646,1653,1654,1660,1693,1721,1753,1852,1987,2173,2238,2365,2413,2425,2428,2455,2462,2486,2518,2621,2653,2677,2684,2731,2734,2746,2794,2876,3011,3127,3131,3133,3134,3165,3181,3187,3189,3190,3193,3194,3196,3229,3245,3260,3277,3292,3308,3358,3373,3388,3418,3433,3448,3478,3493,3508,3613,3630,3644,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 2055,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 773,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 1541,1,1⟩,⟨.covers 1289,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 368,1,1⟩,⟨.covers 624,1,1⟩,⟨.covers 688,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 2256,1,1⟩,⟨.covers 912,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 2272,1,1⟩,⟨.covers 928,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 3712,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_014
namespace C13.Global.FastDual17_015
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,8,10]
def points : Finset C13.Point := {1,7,8,10}
def columns : List Code := [381,471,637,747,829,877,889,892,967,971,979,995,1143,1147,1150,1213,1245,1261,1371,1374,1402,1453,1461,1509,1639,1646,1651,1654,1658,1693,1709,1721,1741,1753,1882,1957,2173,2238,2365,2413,2425,2428,2455,2462,2486,2518,2621,2653,2669,2677,2681,2684,2731,2734,2746,2794,2861,2876,2921,2936,2951,2966,3011,3026,3127,3131,3187,3190,3194,3229,3245,3277,3292,3308,3418,3493,3623,3635,3686,3698,3725,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 267,1,2⟩,⟨.covers 2059,1,1⟩,⟨.covers 147,1,3⟩,⟨.covers 99,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 2121,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 1289,1,2⟩,⟨.covers 3081,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 774,1,3⟩,⟨.covers 1286,1,2⟩,⟨.covers 3078,1,1⟩,⟨.covers 1794,1,4⟩,⟨.covers 3330,1,4⟩,⟨.covers 156,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 564,1,1⟩,⟨.covers 1796,1,4⟩,⟨.covers 3332,1,2⟩,⟨.covers 216,1,1⟩,⟨.covers 368,1,1⟩,⟨.covers 688,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 1584,1,1⟩,⟨.covers 1424,1,4⟩,⟨.covers 2272,1,1⟩,⟨.covers 864,1,1⟩,⟨.covers 1376,1,3⟩,⟨.covers 3168,1,1⟩,⟨.covers 2464,1,2⟩,⟨.covers 1472,1,1⟩,⟨.covers 2496,1,3⟩,⟨.covers 1728,1,1⟩,⟨.incident 8,8,-2⟩,⟨.incident 10,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_015
