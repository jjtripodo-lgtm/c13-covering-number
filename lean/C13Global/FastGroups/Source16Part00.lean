import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source16
namespace C13.Global.FastDual16_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,8]
def points : Finset C13.Point := {1,6,7,8}
def columns : List Code := [829,967,971,979,995,1150,1213,1341,1371,1374,1402,1453,1461,1597,1639,1646,1654,1693,1709,1721,1837,1852,1867,1882,1957,1987,2173,2238,2365,2413,2425,2455,2462,2486,2621,2653,2669,2677,2731,2734,2746,2861,2876,2921,2951,2966,3011,3127,3131,3133,3134,3165,3181,3196,3229,3245,3260,3277,3292,3308,3358,3373,3388,3418,3433,3448,3478,3493,3508,3613,3623,3627,3629,3630,3635,3637,3638,3641,3642,3644,3661,3669,3676,3685,3686,3692,3700,3725,3737,3740,3753,3754,3756,3768,3788]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 83,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 2129,1,1⟩,⟨.covers 1169,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 1808,1,1⟩,⟨.covers 2832,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 928,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 3392,1,1⟩,⟨.covers 3648,1,1⟩,⟨.covers 3456,1,1⟩,⟨.covers 3712,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source16.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source16.rootCodes link16 points rows bound = true := by decide +kernel

end C13.Global.FastDual16_000
namespace C13.Global.FastDual16_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,10]
def points : Finset C13.Point := {1,6,7,10}
def columns : List Code := [829,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1639,1646,1654,1693,1709,1721,1870,1882,1894,1906,1933,1945,1957,1969,2173,2238,2365,2397,2413,2425,2455,2462,2486,2621,2653,2669,2677,2731,2734,2746,2845,2861,2869,2873,2876,2893,2901,2905,2917,2921,2929,2951,2955,2958,2963,2966,2970,2979,2982,2986,2994,3011,3127,3131,3229,3245,3277,3292,3308,3355,3379,3418,3469,3493,3532,3623,3635,3686,3725,3737,3788]
def rows : List LinearRow := [⟨.covers 71,1,12⟩,⟨.covers 1031,1,1⟩,⟨.covers 2055,1,2⟩,⟨.covers 77,1,3⟩,⟨.covers 141,1,6⟩,⟨.covers 533,1,3⟩,⟨.covers 2309,1,3⟩,⟨.covers 89,1,3⟩,⟨.covers 169,1,8⟩,⟨.covers 142,1,3⟩,⟨.covers 270,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 86,1,11⟩,⟨.covers 166,1,4⟩,⟨.covers 3078,1,7⟩,⟨.covers 154,1,2⟩,⟨.covers 106,1,1⟩,⟨.covers 554,1,1⟩,⟨.covers 202,1,12⟩,⟨.covers 1546,1,9⟩,⟨.covers 3082,1,10⟩,⟨.covers 210,1,12⟩,⟨.covers 226,1,12⟩,⟨.covers 2818,1,4⟩,⟨.covers 404,1,3⟩,⟨.covers 1796,1,1⟩,⟨.covers 568,1,3⟩,⟨.covers 216,1,16⟩,⟨.covers 1560,1,2⟩,⟨.covers 232,1,16⟩,⟨.covers 2344,1,3⟩,⟨.covers 2160,1,3⟩,⟨.covers 432,1,1⟩,⟨.covers 688,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 1424,1,5⟩,⟨.covers 2704,1,2⟩,⟨.covers 3600,1,10⟩,⟨.covers 1376,1,11⟩,⟨.covers 2656,1,3⟩,⟨.covers 2464,1,1⟩,⟨.covers 3360,1,10⟩,⟨.covers 1472,1,9⟩,⟨.covers 2496,1,5⟩,⟨.covers 1728,1,13⟩,⟨.covers 2880,1,3⟩,⟨.covers 3392,1,3⟩,⟨.covers 3648,1,3⟩,⟨.covers 1920,1,7⟩,⟨.incident 6,8,-3⟩,⟨.incident 7,8,-4⟩,⟨.incident 10,8,-4⟩]
def bound : Int := 6

theorem column_mask : listMask columns = restrictMask universeMask Source16.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source16.rootCodes link16 points rows bound = true := by decide +kernel

end C13.Global.FastDual16_001
namespace C13.Global.FastDual16_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,8,9]
def points : Finset C13.Point := {1,6,8,9}
def columns : List Code := [445,475,701,743,829,956,967,971,979,995,1150,1213,1341,1371,1374,1402,1453,1461,1468,1498,1597,1639,1646,1654,1693,1721,1724,1766,1852,1987,2173,2231,2235,2237,2238,2269,2285,2365,2413,2425,2455,2462,2477,2485,2486,2492,2537,2621,2653,2677,2717,2731,2734,2745,2746,2748,2773,2876,3011,3127,3131,3133,3134,3165,3181,3196,3229,3245,3251,3253,3254,3257,3258,3260,3277,3292,3308,3358,3373,3388,3418,3433,3448,3478,3493,3508,3613,3630,3644,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 1031,1,4⟩,⟨.covers 2055,1,6⟩,⟨.covers 523,1,2⟩,⟨.covers 1035,1,2⟩,⟨.covers 2059,1,9⟩,⟨.covers 269,1,5⟩,⟨.covers 1037,1,1⟩,⟨.covers 773,1,5⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,6⟩,⟨.covers 89,1,9⟩,⟨.covers 1161,1,2⟩,⟨.covers 1169,1,1⟩,⟨.covers 2577,1,2⟩,⟨.covers 2145,1,1⟩,⟨.covers 1185,1,3⟩,⟨.covers 78,1,2⟩,⟨.covers 142,1,6⟩,⟨.covers 270,1,4⟩,⟨.covers 166,1,3⟩,⟨.covers 198,1,6⟩,⟨.covers 1286,1,5⟩,⟨.covers 2566,1,2⟩,⟨.covers 778,1,9⟩,⟨.covers 1546,1,9⟩,⟨.covers 114,1,9⟩,⟨.covers 178,1,2⟩,⟨.covers 1794,1,11⟩,⟨.covers 2818,1,7⟩,⟨.covers 3330,1,2⟩,⟨.covers 1796,1,11⟩,⟨.covers 2820,1,11⟩,⟨.covers 232,1,9⟩,⟨.covers 624,1,2⟩,⟨.covers 432,1,5⟩,⟨.covers 688,1,5⟩,⟨.covers 1232,1,9⟩,⟨.covers 2256,1,2⟩,⟨.covers 848,1,11⟩,⟨.covers 2384,1,1⟩,⟨.covers 1424,1,2⟩,⟨.covers 2704,1,4⟩,⟨.covers 1248,1,2⟩,⟨.covers 864,1,10⟩,⟨.covers 1376,1,2⟩,⟨.covers 2656,1,7⟩,⟨.covers 928,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 2752,1,3⟩,⟨.covers 3392,1,8⟩,⟨.covers 3648,1,2⟩,⟨.covers 3456,1,3⟩,⟨.covers 3712,1,2⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source16.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source16.rootCodes link16 points rows bound = true := by decide +kernel

end C13.Global.FastDual16_002
namespace C13.Global.FastDual16_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,8,10]
def points : Finset C13.Point := {1,6,8,10}
def columns : List Code := [445,475,701,743,829,941,949,956,967,971,979,995,1150,1213,1371,1374,1402,1453,1461,1498,1639,1646,1654,1693,1709,1717,1721,1766,1882,1957,2173,2231,2235,2237,2238,2269,2285,2365,2413,2425,2455,2462,2477,2485,2486,2492,2537,2621,2653,2669,2677,2717,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2765,2773,2789,2861,2876,2921,2951,2966,2981,2996,3011,3041,3127,3131,3229,3245,3251,3253,3257,3277,3292,3308,3418,3493,3623,3635,3686,3725,3737,3749,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 263,1,1⟩,⟨.covers 1031,1,1⟩,⟨.covers 523,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 3332,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 624,1,1⟩,⟨.covers 2256,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 2880,1,1⟩,⟨.covers 3648,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source16.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source16.rootCodes link16 points rows bound = true := by decide +kernel

end C13.Global.FastDual16_003
namespace C13.Global.FastDual16_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,8,11]
def points : Finset C13.Point := {1,6,8,11}
def columns : List Code := [445,475,701,743,829,941,949,956,967,971,979,995,1150,1213,1341,1371,1374,1402,1453,1461,1468,1498,1597,1639,1646,1654,1693,1709,1717,1721,1724,1766,1837,1852,1867,1882,1957,1972,1987,2002,2173,2231,2235,2238,2269,2285,2413,2425,2455,2462,2486,2537,2653,2669,2677,2731,2734,2739,2742,2746,2765,2773,2921,2966,3127,3131,3165,3181,3251,3254,3258,3277,3292,3308,3433,3478,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 83,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 2307,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 624,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 2608,1,1⟩,⟨.covers 2256,1,1⟩,⟨.covers 1248,1,1⟩,⟨.covers 2848,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2752,1,1⟩,⟨.incident 11,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source16.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source16.rootCodes link16 points rows bound = true := by decide +kernel

end C13.Global.FastDual16_004
namespace C13.Global.FastDual16_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,9,10]
def points : Finset C13.Point := {1,6,9,10}
def columns : List Code := [445,475,701,743,829,925,953,956,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1465,1498,1639,1646,1654,1693,1721,1766,1894,1945,2173,2231,2235,2237,2238,2269,2285,2365,2397,2413,2425,2455,2459,2461,2462,2477,2483,2485,2486,2489,2490,2492,2509,2521,2537,2621,2653,2677,2717,2731,2734,2745,2746,2748,2773,2845,2876,2901,2955,2969,2986,3000,3011,3025,3127,3131,3229,3245,3251,3253,3257,3277,3292,3308,3355,3379,3418,3469,3481,3493,3505,3532,3544,3686,3737]
def rows : List LinearRow := [⟨.covers 263,1,7⟩,⟨.covers 2055,1,4⟩,⟨.covers 523,1,6⟩,⟨.covers 83,1,11⟩,⟨.covers 163,1,2⟩,⟨.covers 2083,1,1⟩,⟨.covers 1539,1,11⟩,⟨.covers 77,1,6⟩,⟨.covers 525,1,2⟩,⟨.covers 1037,1,4⟩,⟨.covers 293,1,2⟩,⟨.covers 773,1,4⟩,⟨.covers 142,1,4⟩,⟨.covers 270,1,7⟩,⟨.covers 2566,1,3⟩,⟨.covers 3078,1,5⟩,⟨.covers 2090,1,1⟩,⟨.covers 778,1,5⟩,⟨.covers 1546,1,11⟩,⟨.covers 3082,1,8⟩,⟨.covers 178,1,3⟩,⟨.covers 1794,1,11⟩,⟨.covers 3330,1,3⟩,⟨.covers 92,1,2⟩,⟨.covers 172,1,2⟩,⟨.covers 1292,1,2⟩,⟨.covers 308,1,2⟩,⟨.covers 2132,1,1⟩,⟨.covers 2244,1,1⟩,⟨.covers 2820,1,4⟩,⟨.covers 3332,1,4⟩,⟨.covers 232,1,2⟩,⟨.covers 368,1,9⟩,⟨.covers 624,1,5⟩,⟨.covers 2160,1,2⟩,⟨.covers 688,1,7⟩,⟨.covers 1200,1,4⟩,⟨.covers 1328,1,2⟩,⟨.covers 1232,1,7⟩,⟨.covers 1616,1,6⟩,⟨.covers 1808,1,11⟩,⟨.covers 3600,1,11⟩,⟨.covers 480,1,9⟩,⟨.covers 1248,1,6⟩,⟨.covers 2656,1,3⟩,⟨.covers 2848,1,4⟩,⟨.covers 3360,1,4⟩,⟨.covers 1472,1,4⟩,⟨.covers 1728,1,5⟩,⟨.covers 2752,1,9⟩,⟨.covers 2880,1,1⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source16.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source16.rootCodes link16 points rows bound = true := by decide +kernel

end C13.Global.FastDual16_005
namespace C13.Global.FastDual16_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,9,11]
def points : Finset C13.Point := {1,6,9,11}
def columns : List Code := [445,475,701,743,829,925,953,956,967,971,979,995,1150,1213,1341,1371,1374,1402,1437,1453,1461,1465,1468,1498,1597,1639,1646,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2173,2231,2235,2238,2269,2285,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2653,2677,2731,2734,2746,2773,2901,2986,3127,3131,3165,3181,3251,3254,3258,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 2055,1,7⟩,⟨.covers 523,1,5⟩,⟨.covers 1035,1,10⟩,⟨.covers 147,1,3⟩,⟨.covers 99,1,9⟩,⟨.covers 1059,1,1⟩,⟨.covers 2563,1,7⟩,⟨.covers 77,1,4⟩,⟨.covers 525,1,4⟩,⟨.covers 293,1,2⟩,⟨.covers 201,1,4⟩,⟨.covers 1161,1,2⟩,⟨.covers 353,1,1⟩,⟨.covers 1185,1,2⟩,⟨.covers 1313,1,2⟩,⟨.covers 3105,1,1⟩,⟨.covers 270,1,8⟩,⟨.covers 526,1,5⟩,⟨.covers 86,1,2⟩,⟨.covers 390,1,1⟩,⟨.covers 774,1,8⟩,⟨.covers 2566,1,7⟩,⟨.covers 3078,1,3⟩,⟨.covers 114,1,6⟩,⟨.covers 178,1,1⟩,⟨.covers 210,1,2⟩,⟨.covers 2818,1,12⟩,⟨.covers 3586,1,12⟩,⟨.covers 108,1,2⟩,⟨.covers 2316,1,3⟩,⟨.covers 1548,1,2⟩,⟨.covers 308,1,2⟩,⟨.covers 3204,1,3⟩,⟨.covers 1796,1,2⟩,⟨.covers 2820,1,13⟩,⟨.covers 3332,1,2⟩,⟨.covers 3588,1,13⟩,⟨.covers 184,1,2⟩,⟨.covers 232,1,3⟩,⟨.covers 368,1,4⟩,⟨.covers 2352,1,8⟩,⟨.covers 1584,1,2⟩,⟨.covers 2608,1,9⟩,⟨.covers 1232,1,7⟩,⟨.covers 912,1,5⟩,⟨.covers 3216,1,3⟩,⟨.covers 2656,1,4⟩,⟨.covers 3168,1,6⟩,⟨.covers 2496,1,1⟩,⟨.covers 1728,1,10⟩,⟨.covers 2752,1,13⟩,⟨.covers 3392,1,3⟩,⟨.incident 6,8,-1⟩,⟨.incident 11,8,-3⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source16.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source16.rootCodes link16 points rows bound = true := by decide +kernel

end C13.Global.FastDual16_006
namespace C13.Global.FastDual16_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,10,11]
def points : Finset C13.Point := {1,6,10,11}
def columns : List Code := [445,475,701,743,829,925,941,949,953,956,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1465,1498,1639,1646,1654,1693,1709,1717,1721,1766,1870,1882,1894,1906,1933,1945,1957,1969,2173,2231,2235,2238,2269,2285,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2653,2669,2677,2731,2734,2739,2742,2746,2765,2773,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3251,3277,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 263,1,1⟩,⟨.covers 523,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 86,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 3332,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 2464,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source16.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source16.rootCodes link16 points rows bound = true := by decide +kernel

end C13.Global.FastDual16_007
