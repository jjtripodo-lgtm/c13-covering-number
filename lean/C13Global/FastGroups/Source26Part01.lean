import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source26
namespace C13.Global.FastDual26_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,10]
def points : Finset C13.Point := {1,6,7,10}
def columns : List Code := [829,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1639,1646,1654,1693,1709,1721,1870,1882,1894,1906,1933,1945,1957,1969,2173,2238,2365,2397,2413,2425,2455,2462,2486,2621,2653,2669,2677,2731,2734,2746,2845,2861,2869,2873,2876,2893,2901,2905,2917,2921,2929,2951,2955,2958,2963,2966,2970,2979,2982,2986,2994,3011,3127,3131,3229,3245,3277,3292,3308,3355,3379,3418,3469,3493,3532,3623,3635,3686,3725,3737,3788]
def rows : List LinearRow := [⟨.covers 75,1,4⟩,⟨.covers 139,1,2⟩,⟨.covers 83,1,4⟩,⟨.covers 147,1,2⟩,⟨.covers 99,1,9⟩,⟨.covers 77,1,4⟩,⟨.covers 141,1,2⟩,⟨.covers 149,1,2⟩,⟨.covers 101,1,4⟩,⟨.covers 89,1,4⟩,⟨.covers 169,1,2⟩,⟨.covers 201,1,13⟩,⟨.covers 78,1,4⟩,⟨.covers 142,1,2⟩,⟨.covers 278,1,2⟩,⟨.covers 166,1,2⟩,⟨.covers 198,1,20⟩,⟨.covers 1286,1,7⟩,⟨.covers 154,1,2⟩,⟨.covers 106,1,9⟩,⟨.covers 210,1,13⟩,⟨.covers 226,1,11⟩,⟨.covers 2818,1,2⟩,⟨.covers 212,1,9⟩,⟨.covers 596,1,4⟩,⟨.covers 228,1,20⟩,⟨.covers 1316,1,2⟩,⟨.covers 3332,1,2⟩,⟨.covers 1560,1,2⟩,⟨.covers 360,1,4⟩,⟨.covers 680,1,2⟩,⟨.covers 1800,1,2⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,9⟩,⟨.covers 3152,1,9⟩,⟨.covers 1424,1,2⟩,⟨.covers 2704,1,2⟩,⟨.covers 3216,1,2⟩,⟨.covers 2656,1,4⟩,⟨.covers 2464,1,2⟩,⟨.covers 1824,1,4⟩,⟨.covers 1472,1,4⟩,⟨.covers 2496,1,13⟩,⟨.covers 1728,1,20⟩,⟨.covers 2880,1,4⟩,⟨.incident 6,8,-13⟩,⟨.incident 7,8,-7⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source26.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source26.rootCodes link26 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual26_008
namespace C13.Global.FastDual26_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,9,10]
def points : Finset C13.Point := {1,6,9,10}
def columns : List Code := [445,475,701,743,829,925,953,956,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1465,1498,1639,1646,1654,1693,1721,1766,1894,1945,2173,2231,2235,2237,2238,2269,2285,2365,2397,2413,2425,2455,2459,2461,2462,2477,2483,2485,2486,2489,2490,2492,2509,2521,2537,2621,2653,2677,2717,2731,2734,2745,2746,2748,2773,2845,2876,2901,2955,2969,2986,3000,3011,3025,3127,3131,3229,3245,3251,3253,3257,3277,3292,3308,3355,3379,3418,3469,3481,3493,3505,3532,3544,3686,3737]
def rows : List LinearRow := [⟨.covers 263,1,1⟩,⟨.covers 1031,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 86,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 688,1,1⟩,⟨.covers 1328,1,1⟩,⟨.covers 1584,1,1⟩,⟨.covers 848,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source26.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source26.rootCodes link26 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual26_009
namespace C13.Global.FastDual26_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,9,11]
def points : Finset C13.Point := {1,6,9,11}
def columns : List Code := [445,475,701,743,829,925,953,956,967,971,979,995,1150,1213,1341,1371,1374,1402,1437,1453,1461,1465,1468,1498,1597,1639,1646,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2173,2231,2235,2238,2269,2285,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2653,2677,2731,2734,2746,2773,2901,2986,3127,3131,3165,3181,3251,3254,3258,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 2055,1,4⟩,⟨.covers 75,1,1⟩,⟨.covers 1035,1,5⟩,⟨.covers 147,1,1⟩,⟨.covers 1539,1,13⟩,⟨.covers 2563,1,16⟩,⟨.covers 77,1,1⟩,⟨.covers 525,1,4⟩,⟨.covers 201,1,2⟩,⟨.covers 777,1,4⟩,⟨.covers 3081,1,3⟩,⟨.covers 1169,1,4⟩,⟨.covers 2337,1,1⟩,⟨.covers 3105,1,1⟩,⟨.covers 270,1,5⟩,⟨.covers 526,1,4⟩,⟨.covers 198,1,10⟩,⟨.covers 390,1,2⟩,⟨.covers 2566,1,3⟩,⟨.covers 3078,1,3⟩,⟨.covers 106,1,5⟩,⟨.covers 778,1,6⟩,⟨.covers 210,1,1⟩,⟨.covers 2818,1,10⟩,⟨.covers 3586,1,16⟩,⟨.covers 300,1,4⟩,⟨.covers 2316,1,1⟩,⟨.covers 1548,1,4⟩,⟨.covers 2572,1,10⟩,⟨.covers 228,1,2⟩,⟨.covers 1220,1,1⟩,⟨.covers 2820,1,8⟩,⟨.covers 3332,1,1⟩,⟨.covers 3588,1,6⟩,⟨.covers 232,1,2⟩,⟨.covers 3336,1,1⟩,⟨.covers 688,1,4⟩,⟨.covers 2352,1,6⟩,⟨.covers 1584,1,4⟩,⟨.covers 1232,1,4⟩,⟨.covers 848,1,6⟩,⟨.covers 1616,1,9⟩,⟨.covers 912,1,4⟩,⟨.covers 2704,1,12⟩,⟨.covers 3216,1,2⟩,⟨.covers 864,1,13⟩,⟨.covers 2656,1,15⟩,⟨.covers 3168,1,2⟩,⟨.covers 2496,1,3⟩,⟨.covers 2752,1,3⟩,⟨.incident 1,8,-1⟩,⟨.incident 9,8,-8⟩,⟨.incident 11,8,-3⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source26.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source26.rootCodes link26 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual26_010
namespace C13.Global.FastDual26_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,10,11]
def points : Finset C13.Point := {1,6,10,11}
def columns : List Code := [445,475,701,743,829,925,941,949,953,956,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1465,1498,1639,1646,1654,1693,1709,1717,1721,1766,1870,1882,1894,1906,1933,1945,1957,1969,2173,2231,2235,2238,2269,2285,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2653,2669,2677,2731,2734,2739,2742,2746,2765,2773,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3251,3277,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 263,1,6⟩,⟨.covers 1031,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 523,1,5⟩,⟨.covers 83,1,1⟩,⟨.covers 99,1,6⟩,⟨.covers 1283,1,4⟩,⟨.covers 77,1,3⟩,⟨.covers 1037,1,4⟩,⟨.covers 293,1,3⟩,⟨.covers 2309,1,2⟩,⟨.covers 1541,1,4⟩,⟨.covers 89,1,2⟩,⟨.covers 537,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 1289,1,4⟩,⟨.covers 2569,1,2⟩,⟨.covers 3081,1,8⟩,⟨.covers 142,1,6⟩,⟨.covers 278,1,1⟩,⟨.covers 1286,1,10⟩,⟨.covers 2566,1,2⟩,⟨.covers 3078,1,13⟩,⟨.covers 154,1,2⟩,⟨.covers 106,1,8⟩,⟨.covers 554,1,2⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,7⟩,⟨.covers 3330,1,11⟩,⟨.covers 3586,1,15⟩,⟨.covers 116,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 788,1,1⟩,⟨.covers 2580,1,2⟩,⟨.covers 2820,1,1⟩,⟨.covers 3332,1,9⟩,⟨.covers 3588,1,9⟩,⟨.covers 120,1,2⟩,⟨.covers 568,1,1⟩,⟨.covers 664,1,3⟩,⟨.covers 360,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 2160,1,2⟩,⟨.covers 1200,1,3⟩,⟨.covers 720,1,5⟩,⟨.covers 2384,1,3⟩,⟨.covers 1616,1,10⟩,⟨.covers 3152,1,15⟩,⟨.covers 1424,1,4⟩,⟨.covers 2704,1,2⟩,⟨.covers 1248,1,3⟩,⟨.covers 2656,1,5⟩,⟨.covers 2464,1,7⟩,⟨.covers 1696,1,3⟩,⟨.covers 3232,1,12⟩,⟨.covers 1824,1,1⟩,⟨.covers 1472,1,5⟩,⟨.covers 1728,1,5⟩,⟨.covers 2880,1,1⟩,⟨.incident 10,8,-5⟩,⟨.incident 11,8,-4⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source26.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source26.rootCodes link26 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual26_011
namespace C13.Global.FastDual26_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,7]
def points : Finset C13.Point := {2,3,6,7}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,979,995,1371,1402,1447,1461,1639,1654,1691,1721,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1955,1957,1969,1987,2411,2425,2455,2486,2647,2677,2731,2746,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2966,2979,2986,2994,3011,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3477,3478,3493,3494,3508,3532,3635,3655,3669,3670,3685,3686,3700,3723,3737,3738,3753,3754,3768,3788,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 135,1,11⟩,⟨.covers 139,1,11⟩,⟨.covers 77,1,33⟩,⟨.covers 149,1,13⟩,⟨.covers 169,1,13⟩,⟨.covers 1409,1,6⟩,⟨.covers 1665,1,6⟩,⟨.covers 78,1,33⟩,⟨.covers 166,1,9⟩,⟨.covers 154,1,9⟩,⟨.covers 210,1,33⟩,⟨.covers 226,1,33⟩,⟨.covers 2434,1,6⟩,⟨.covers 2690,1,6⟩,⟨.covers 92,1,33⟩,⟨.covers 108,1,33⟩,⟨.covers 1412,1,7⟩,⟨.covers 2436,1,4⟩,⟨.covers 1672,1,7⟩,⟨.covers 2696,1,4⟩,⟨.covers 1200,1,4⟩,⟨.covers 2224,1,7⟩,⟨.covers 1424,1,4⟩,⟨.covers 2704,1,7⟩,⟨.covers 2464,1,7⟩,⟨.covers 1696,1,4⟩,⟨.covers 1472,1,22⟩,⟨.incident 7,8,-33⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source26.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source26.rootCodes link26 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual26_012
namespace C13.Global.FastDual26_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,9]
def points : Finset C13.Point := {2,3,6,9}
def columns : List Code := [379,439,631,699,829,830,953,954,956,979,995,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1721,1722,1766,1852,1894,1945,1976,1987,2018,2411,2425,2455,2483,2485,2486,2537,2647,2677,2731,2745,2746,2773,2876,2901,2986,3000,3011,3025,3251,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3475,3477,3478,3491,3493,3494,3505,3506,3508,3529,3530,3532,3544,3560,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 77,1,18⟩,⟨.covers 269,1,18⟩,⟨.covers 149,1,5⟩,⟨.covers 101,1,12⟩,⟨.covers 1061,1,2⟩,⟨.covers 2309,1,5⟩,⟨.covers 89,1,1⟩,⟨.covers 169,1,3⟩,⟨.covers 1289,1,4⟩,⟨.covers 2569,1,2⟩,⟨.covers 2145,1,2⟩,⟨.covers 1185,1,3⟩,⟨.covers 78,1,18⟩,⟨.covers 270,1,9⟩,⟨.covers 86,1,2⟩,⟨.covers 2070,1,2⟩,⟨.covers 166,1,5⟩,⟨.covers 774,1,8⟩,⟨.covers 1286,1,5⟩,⟨.covers 2566,1,11⟩,⟨.covers 154,1,3⟩,⟨.covers 1050,1,1⟩,⟨.covers 106,1,2⟩,⟨.covers 2314,1,2⟩,⟨.covers 1546,1,2⟩,⟨.covers 210,1,2⟩,⟨.covers 2322,1,3⟩,⟨.covers 2594,1,2⟩,⟨.covers 1794,1,1⟩,⟨.covers 2818,1,3⟩,⟨.covers 92,1,10⟩,⟨.covers 172,1,7⟩,⟨.covers 1548,1,18⟩,⟨.covers 2572,1,9⟩,⟨.covers 180,1,5⟩,⟨.covers 212,1,7⟩,⟨.covers 228,1,9⟩,⟨.covers 2820,1,9⟩,⟨.covers 3332,1,5⟩,⟨.covers 3588,1,2⟩,⟨.covers 120,1,3⟩,⟨.covers 232,1,1⟩,⟨.covers 3592,1,3⟩,⟨.covers 2384,1,1⟩,⟨.covers 1616,1,12⟩,⟨.covers 2704,1,2⟩,⟨.covers 1920,1,2⟩,⟨.incident 2,8,-11⟩,⟨.incident 3,8,-4⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source26.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source26.rootCodes link26 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual26_013
namespace C13.Global.FastDual26_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,10]
def points : Finset C13.Point := {2,3,6,10}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1498,1639,1654,1691,1715,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2411,2425,2455,2483,2485,2486,2537,2647,2677,2731,2739,2745,2746,2773,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2965,2966,2979,2985,2986,2993,2994,2996,3000,3011,3025,3041,3251,3277,3278,3292,3308,3379,3418,3493,3505,3532,3544,3635,3686,3737,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 71,1,5⟩,⟨.covers 2055,1,2⟩,⟨.covers 1035,1,9⟩,⟨.covers 2059,1,2⟩,⟨.covers 77,1,4⟩,⟨.covers 269,1,11⟩,⟨.covers 149,1,4⟩,⟨.covers 101,1,4⟩,⟨.covers 2309,1,2⟩,⟨.covers 1541,1,2⟩,⟨.covers 89,1,2⟩,⟨.covers 169,1,4⟩,⟨.covers 201,1,7⟩,⟨.covers 2569,1,2⟩,⟨.covers 78,1,9⟩,⟨.covers 270,1,11⟩,⟨.covers 86,1,2⟩,⟨.covers 2070,1,2⟩,⟨.covers 390,1,2⟩,⟨.covers 1286,1,9⟩,⟨.covers 154,1,2⟩,⟨.covers 106,1,7⟩,⟨.covers 2314,1,2⟩,⟨.covers 3082,1,2⟩,⟨.covers 210,1,4⟩,⟨.covers 226,1,11⟩,⟨.covers 2210,1,2⟩,⟨.covers 2690,1,2⟩,⟨.covers 3330,1,7⟩,⟨.covers 3586,1,2⟩,⟨.covers 92,1,5⟩,⟨.covers 108,1,11⟩,⟨.covers 1292,1,5⟩,⟨.covers 1548,1,2⟩,⟨.covers 180,1,5⟩,⟨.covers 2820,1,5⟩,⟨.covers 120,1,2⟩,⟨.covers 184,1,5⟩,⟨.covers 216,1,5⟩,⟨.covers 1800,1,2⟩,⟨.covers 2824,1,5⟩,⟨.covers 3592,1,9⟩,⟨.covers 2160,1,7⟩,⟨.covers 1200,1,2⟩,⟨.covers 720,1,7⟩,⟨.covers 1616,1,9⟩,⟨.covers 1376,1,2⟩,⟨.covers 3360,1,4⟩,⟨.covers 3616,1,9⟩,⟨.covers 2880,1,4⟩,⟨.covers 1920,1,9⟩,⟨.covers 3456,1,5⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source26.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source26.rootCodes link26 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual26_014
namespace C13.Global.FastDual26_015
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,11]
def points : Finset C13.Point := {2,3,6,11}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1946,1955,1957,1958,1969,1970,1972,1976,1987,2002,2018,2411,2425,2455,2483,2486,2537,2647,2677,2731,2739,2746,2773,2839,2859,2867,2901,2921,2929,2966,2986,2994,3251,3277,3278,3292,3308,3379,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 3105,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 2224,1,1⟩,⟨.covers 2384,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2880,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source26.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source26.rootCodes link26 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual26_015
