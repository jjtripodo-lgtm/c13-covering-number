import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source15
namespace C13.Global.FastDual15_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,8]
def points : Finset C13.Point := {1,3,6,8}
def columns : List Code := [701,743,829,949,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1724,1766,1852,1882,1957,1972,1987,2002,2231,2285,2413,2425,2455,2485,2486,2537,2677,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2773,2789,2861,2876,2921,2951,2966,2981,2996,3011,3041,3127,3251,3253,3254,3277,3292,3308,3418,3433,3448,3478,3493,3508,3623,3635,3637,3638,3669,3685,3686,3700,3725,3733,3737,3740,3747,3749,3750,3753,3754,3756,3761,3762,3764,3768,3781,3788,3796,3812]
def rows : List LinearRow := [⟨.covers 71,1,11⟩,⟨.covers 139,1,11⟩,⟨.covers 83,1,3⟩,⟨.covers 2307,1,11⟩,⟨.covers 269,1,11⟩,⟨.covers 1037,1,3⟩,⟨.covers 89,1,9⟩,⟨.covers 201,1,9⟩,⟨.covers 1073,1,3⟩,⟨.covers 657,1,3⟩,⟨.covers 3089,1,3⟩,⟨.covers 142,1,11⟩,⟨.covers 1286,1,6⟩,⟨.covers 3078,1,6⟩,⟨.covers 106,1,11⟩,⟨.covers 202,1,11⟩,⟨.covers 778,1,11⟩,⟨.covers 2314,1,11⟩,⟨.covers 178,1,6⟩,⟨.covers 3586,1,6⟩,⟨.covers 92,1,6⟩,⟨.covers 156,1,3⟩,⟨.covers 1548,1,3⟩,⟨.covers 184,1,6⟩,⟨.covers 232,1,3⟩,⟨.covers 3592,1,6⟩,⟨.covers 624,1,11⟩,⟨.covers 720,1,6⟩,⟨.covers 2256,1,3⟩,⟨.covers 2832,1,11⟩,⟨.covers 1248,1,9⟩,⟨.covers 864,1,11⟩,⟨.covers 1824,1,9⟩,⟨.covers 3360,1,11⟩,⟨.covers 1728,1,3⟩,⟨.covers 1920,1,3⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source15.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source15.rootCodes link15 points rows bound = true := by decide +kernel

end C13.Global.FastDual15_000
namespace C13.Global.FastDual15_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,9]
def points : Finset C13.Point := {1,3,6,9}
def columns : List Code := [701,743,829,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2231,2285,2413,2425,2455,2483,2485,2486,2537,2677,2731,2734,2745,2746,2748,2773,2876,2901,2986,3000,3011,3025,3127,3251,3253,3254,3277,3292,3308,3351,3379,3381,3382,3405,3417,3418,3420,3433,3436,3448,3475,3477,3478,3493,3505,3506,3508,3529,3532,3544,3560,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 75,1,1⟩,⟨.covers 139,1,2⟩,⟨.covers 83,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 99,1,2⟩,⟨.covers 142,1,2⟩,⟨.covers 86,1,2⟩,⟨.covers 774,1,2⟩,⟨.covers 3078,1,1⟩,⟨.covers 106,1,2⟩,⟨.covers 202,1,2⟩,⟨.covers 1546,1,2⟩,⟨.covers 178,1,1⟩,⟨.covers 2818,1,2⟩,⟨.covers 3330,1,1⟩,⟨.covers 1728,1,2⟩,⟨.incident 1,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source15.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source15.rootCodes link15 points rows bound = true := by decide +kernel

end C13.Global.FastDual15_001
namespace C13.Global.FastDual15_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,8,10]
def points : Finset C13.Point := {1,3,8,10}
def columns : List Code := [247,251,253,254,381,471,499,501,502,505,506,508,701,743,755,757,758,761,762,764,829,889,892,949,956,967,979,982,995,997,1009,1010,1012,1016,1143,1245,1267,1269,1270,1273,1274,1276,1371,1374,1402,1461,1498,1509,1521,1522,1524,1528,1639,1651,1654,1693,1717,1721,1753,1756,1765,1766,1777,1778,1780,1784,1882,1957,2032,2231,2285,2291,2293,2294,2297,2298,2300,2413,2425,2428,2455,2485,2486,2515,2518,2533,2537,2545,2546,2548,2552,2677,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2773,2787,2789,2790,2793,2794,2796,2801,2802,2804,2808,2861,2876,2921,2936,2951,2966,2981,2996,3011,3026,3041,3056,3127,3187,3190,3251,3253,3277,3289,3292,3301,3308,3313,3314,3316,3320,3418,3493,3568,3623,3635,3686,3698,3725,3737,3749,3761,3788,3800,3812,3824]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 1031,1,1⟩,⟨.covers 267,1,34⟩,⟨.covers 523,1,34⟩,⟨.covers 147,1,7⟩,⟨.covers 2067,1,1⟩,⟨.covers 99,1,2⟩,⟨.covers 2307,1,4⟩,⟨.covers 1539,1,3⟩,⟨.covers 77,1,6⟩,⟨.covers 269,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 777,1,8⟩,⟨.covers 3081,1,5⟩,⟨.covers 270,1,34⟩,⟨.covers 526,1,34⟩,⟨.covers 198,1,1⟩,⟨.covers 774,1,5⟩,⟨.covers 3078,1,7⟩,⟨.covers 154,1,23⟩,⟨.covers 778,1,34⟩,⟨.covers 2314,1,34⟩,⟨.covers 1074,1,5⟩,⟨.covers 2098,1,2⟩,⟨.covers 402,1,3⟩,⟨.covers 2194,1,1⟩,⟨.covers 610,1,2⟩,⟨.covers 1122,1,2⟩,⟨.covers 706,1,5⟩,⟨.covers 2818,1,7⟩,⟨.covers 3586,1,5⟩,⟨.covers 156,1,7⟩,⟨.covers 540,1,1⟩,⟨.covers 108,1,3⟩,⟨.covers 2316,1,3⟩,⟨.covers 1548,1,5⟩,⟨.covers 312,1,5⟩,⟨.covers 568,1,2⟩,⟨.covers 664,1,1⟩,⟨.covers 1176,1,3⟩,⟨.covers 360,1,2⟩,⟨.covers 2152,1,2⟩,⟨.covers 2248,1,5⟩,⟨.covers 2824,1,5⟩,⟨.covers 3592,1,8⟩,⟨.incident 1,8,-16⟩,⟨.incident 3,8,-17⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source15.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source15.rootCodes link15 points rows bound = true := by decide +kernel

end C13.Global.FastDual15_002
namespace C13.Global.FastDual15_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,8]
def points : Finset C13.Point := {1,6,7,8}
def columns : List Code := [829,967,971,979,995,1150,1213,1341,1371,1374,1402,1453,1461,1597,1639,1646,1654,1693,1709,1721,1837,1852,1867,1882,1957,1987,2173,2238,2365,2413,2425,2455,2462,2486,2621,2653,2669,2677,2731,2734,2746,2861,2876,2921,2951,2966,3011,3127,3131,3133,3134,3165,3181,3196,3229,3245,3260,3277,3292,3308,3358,3373,3388,3418,3433,3448,3478,3493,3508,3613,3623,3627,3629,3630,3635,3637,3638,3641,3642,3644,3661,3669,3676,3685,3686,3692,3700,3725,3737,3740,3753,3754,3756,3768,3788]
def rows : List LinearRow := [⟨.covers 1031,1,6⟩,⟨.covers 2059,1,6⟩,⟨.covers 83,1,5⟩,⟨.covers 147,1,1⟩,⟨.covers 77,1,2⟩,⟨.covers 141,1,2⟩,⟨.covers 269,1,3⟩,⟨.covers 1157,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 777,1,2⟩,⟨.covers 2129,1,3⟩,⟨.covers 1169,1,3⟩,⟨.covers 2337,1,1⟩,⟨.covers 270,1,6⟩,⟨.covers 526,1,6⟩,⟨.covers 198,1,6⟩,⟨.covers 202,1,3⟩,⟨.covers 114,1,6⟩,⟨.covers 178,1,6⟩,⟨.covers 226,1,6⟩,⟨.covers 216,1,6⟩,⟨.covers 232,1,6⟩,⟨.covers 1800,1,1⟩,⟨.covers 2384,1,1⟩,⟨.covers 1424,1,2⟩,⟨.covers 1808,1,5⟩,⟨.covers 2832,1,6⟩,⟨.covers 2656,1,3⟩,⟨.covers 1696,1,3⟩,⟨.covers 1472,1,6⟩,⟨.covers 2496,1,6⟩,⟨.covers 3392,1,5⟩,⟨.covers 3648,1,3⟩,⟨.covers 3456,1,4⟩,⟨.covers 3712,1,3⟩]
def bound : Int := 6

theorem column_mask : listMask columns = restrictMask universeMask Source15.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source15.rootCodes link15 points rows bound = true := by decide +kernel

end C13.Global.FastDual15_003
namespace C13.Global.FastDual15_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,10]
def points : Finset C13.Point := {1,6,7,10}
def columns : List Code := [829,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1639,1646,1654,1693,1709,1721,1870,1882,1894,1906,1933,1945,1957,1969,2173,2238,2365,2397,2413,2425,2455,2462,2486,2621,2653,2669,2677,2731,2734,2746,2845,2861,2869,2873,2876,2893,2901,2905,2917,2921,2929,2951,2955,2958,2963,2966,2970,2979,2982,2986,2994,3011,3127,3131,3229,3245,3277,3292,3308,3355,3379,3418,3469,3493,3532,3623,3635,3686,3725,3737,3788]
def rows : List LinearRow := [⟨.covers 71,1,9⟩,⟨.covers 135,1,4⟩,⟨.covers 1031,1,4⟩,⟨.covers 2059,1,3⟩,⟨.covers 77,1,5⟩,⟨.covers 141,1,6⟩,⟨.covers 533,1,2⟩,⟨.covers 89,1,2⟩,⟨.covers 169,1,3⟩,⟨.covers 78,1,2⟩,⟨.covers 142,1,4⟩,⟨.covers 86,1,12⟩,⟨.covers 166,1,2⟩,⟨.covers 3078,1,3⟩,⟨.covers 202,1,14⟩,⟨.covers 1546,1,11⟩,⟨.covers 3082,1,4⟩,⟨.covers 210,1,14⟩,⟨.covers 226,1,14⟩,⟨.covers 2818,1,2⟩,⟨.covers 404,1,3⟩,⟨.covers 1316,1,2⟩,⟨.covers 184,1,1⟩,⟨.covers 216,1,19⟩,⟨.covers 664,1,3⟩,⟨.covers 232,1,19⟩,⟨.covers 360,1,2⟩,⟨.covers 680,1,1⟩,⟨.covers 2344,1,1⟩,⟨.covers 2160,1,2⟩,⟨.covers 1200,1,1⟩,⟨.covers 2384,1,2⟩,⟨.covers 1616,1,2⟩,⟨.covers 1424,1,3⟩,⟨.covers 2704,1,1⟩,⟨.covers 3600,1,7⟩,⟨.covers 1376,1,12⟩,⟨.covers 2656,1,2⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,2⟩,⟨.covers 3360,1,7⟩,⟨.covers 1472,1,3⟩,⟨.covers 2496,1,8⟩,⟨.covers 1728,1,9⟩,⟨.covers 2880,1,4⟩,⟨.covers 3392,1,8⟩,⟨.covers 3648,1,9⟩,⟨.covers 1920,1,6⟩,⟨.incident 6,8,-7⟩,⟨.incident 7,8,-5⟩,⟨.incident 10,8,-5⟩]
def bound : Int := 3

theorem column_mask : listMask columns = restrictMask universeMask Source15.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source15.rootCodes link15 points rows bound = true := by decide +kernel

end C13.Global.FastDual15_004
namespace C13.Global.FastDual15_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,8,9]
def points : Finset C13.Point := {1,6,8,9}
def columns : List Code := [445,475,701,743,829,956,967,971,979,995,1150,1213,1341,1371,1374,1402,1453,1461,1468,1498,1597,1639,1646,1654,1693,1721,1724,1766,1852,1987,2173,2231,2235,2237,2238,2269,2285,2365,2413,2425,2455,2462,2477,2485,2486,2492,2537,2621,2653,2677,2717,2731,2734,2745,2746,2748,2773,2876,3011,3127,3131,3133,3134,3165,3181,3196,3229,3245,3251,3253,3254,3257,3258,3260,3277,3292,3308,3358,3373,3388,3418,3433,3448,3478,3493,3508,3613,3630,3644,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 263,1,12⟩,⟨.covers 1031,1,12⟩,⟨.covers 523,1,6⟩,⟨.covers 1035,1,6⟩,⟨.covers 2059,1,6⟩,⟨.covers 77,1,4⟩,⟨.covers 269,1,3⟩,⟨.covers 2061,1,3⟩,⟨.covers 533,1,3⟩,⟨.covers 1157,1,3⟩,⟨.covers 777,1,6⟩,⟨.covers 1289,1,6⟩,⟨.covers 2129,1,2⟩,⟨.covers 1169,1,6⟩,⟨.covers 2145,1,2⟩,⟨.covers 78,1,4⟩,⟨.covers 142,1,3⟩,⟨.covers 270,1,8⟩,⟨.covers 166,1,3⟩,⟨.covers 2566,1,6⟩,⟨.covers 106,1,2⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,6⟩,⟨.covers 114,1,6⟩,⟨.covers 178,1,6⟩,⟨.covers 1794,1,12⟩,⟨.covers 3330,1,3⟩,⟨.covers 216,1,3⟩,⟨.covers 232,1,3⟩,⟨.covers 1800,1,12⟩,⟨.covers 2824,1,12⟩,⟨.covers 624,1,5⟩,⟨.covers 432,1,3⟩,⟨.covers 688,1,6⟩,⟨.covers 720,1,2⟩,⟨.covers 1232,1,9⟩,⟨.covers 848,1,10⟩,⟨.covers 2384,1,8⟩,⟨.covers 1616,1,1⟩,⟨.covers 1248,1,9⟩,⟨.covers 864,1,9⟩,⟨.covers 1376,1,4⟩,⟨.covers 928,1,3⟩,⟨.covers 2496,1,7⟩,⟨.covers 2752,1,5⟩,⟨.covers 3648,1,6⟩,⟨.covers 3456,1,9⟩,⟨.covers 3712,1,6⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source15.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source15.rootCodes link15 points rows bound = true := by decide +kernel

end C13.Global.FastDual15_005
namespace C13.Global.FastDual15_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,8,10]
def points : Finset C13.Point := {1,6,8,10}
def columns : List Code := [445,475,701,743,829,941,949,956,967,971,979,995,1150,1213,1371,1374,1402,1453,1461,1498,1639,1646,1654,1693,1709,1717,1721,1766,1882,1957,2173,2231,2235,2237,2238,2269,2285,2365,2413,2425,2455,2462,2477,2485,2486,2492,2537,2621,2653,2669,2677,2717,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2765,2773,2789,2861,2876,2921,2951,2966,2981,2996,3011,3041,3127,3131,3229,3245,3251,3253,3257,3277,3292,3308,3418,3493,3623,3635,3686,3725,3737,3749,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 263,1,1⟩,⟨.covers 1031,1,1⟩,⟨.covers 523,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 1584,1,1⟩,⟨.covers 2256,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 1824,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 2880,1,1⟩,⟨.covers 3648,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source15.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source15.rootCodes link15 points rows bound = true := by decide +kernel

end C13.Global.FastDual15_006
namespace C13.Global.FastDual15_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,8,11]
def points : Finset C13.Point := {1,6,8,11}
def columns : List Code := [445,475,701,743,829,941,949,956,967,971,979,995,1150,1213,1341,1371,1374,1402,1453,1461,1468,1498,1597,1639,1646,1654,1693,1709,1717,1721,1724,1766,1837,1852,1867,1882,1957,1972,1987,2002,2173,2231,2235,2238,2269,2285,2413,2425,2455,2462,2486,2537,2653,2669,2677,2731,2734,2739,2742,2746,2765,2773,2921,2966,3127,3131,3165,3181,3251,3254,3258,3277,3292,3308,3433,3478,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 263,1,8⟩,⟨.covers 1031,1,12⟩,⟨.covers 2059,1,8⟩,⟨.covers 83,1,12⟩,⟨.covers 163,1,2⟩,⟨.covers 2307,1,6⟩,⟨.covers 2563,1,1⟩,⟨.covers 77,1,5⟩,⟨.covers 269,1,4⟩,⟨.covers 1157,1,2⟩,⟨.covers 537,1,1⟩,⟨.covers 1169,1,1⟩,⟨.covers 1553,1,3⟩,⟨.covers 2577,1,1⟩,⟨.covers 3089,1,3⟩,⟨.covers 78,1,2⟩,⟨.covers 526,1,9⟩,⟨.covers 86,1,8⟩,⟨.covers 198,1,3⟩,⟨.covers 650,1,2⟩,⟨.covers 778,1,10⟩,⟨.covers 2314,1,14⟩,⟨.covers 3082,1,3⟩,⟨.covers 114,1,1⟩,⟨.covers 178,1,3⟩,⟨.covers 226,1,6⟩,⟨.covers 2818,1,14⟩,⟨.covers 3330,1,14⟩,⟨.covers 1292,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 2572,1,3⟩,⟨.covers 568,1,2⟩,⟨.covers 3208,1,3⟩,⟨.covers 1800,1,2⟩,⟨.covers 2824,1,10⟩,⟨.covers 3336,1,2⟩,⟨.covers 3592,1,1⟩,⟨.covers 624,1,2⟩,⟨.covers 432,1,2⟩,⟨.covers 1328,1,2⟩,⟨.covers 2608,1,6⟩,⟨.covers 2256,1,5⟩,⟨.covers 2384,1,10⟩,⟨.covers 3152,1,2⟩,⟨.covers 1248,1,2⟩,⟨.covers 1376,1,8⟩,⟨.covers 928,1,3⟩,⟨.covers 2464,1,10⟩,⟨.covers 3232,1,5⟩,⟨.covers 1472,1,12⟩,⟨.covers 2752,1,2⟩,⟨.covers 3648,1,1⟩,⟨.incident 1,8,-4⟩,⟨.incident 11,8,-3⟩]
def bound : Int := 8

theorem column_mask : listMask columns = restrictMask universeMask Source15.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source15.rootCodes link15 points rows bound = true := by decide +kernel

end C13.Global.FastDual15_007
