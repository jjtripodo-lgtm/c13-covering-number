import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source53
namespace C13.Global.FastDual53_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,9]
def points : Finset C13.Point := {1,6,7,9}
def columns : List Code := [829,967,971,979,995,1150,1213,1341,1371,1374,1402,1437,1453,1461,1597,1639,1646,1654,1693,1721,1821,1852,1863,1894,1945,1987,2173,2238,2365,2397,2413,2425,2455,2462,2486,2621,2653,2677,2731,2734,2746,2845,2876,2901,2955,2986,3011,3127,3131,3133,3134,3165,3181,3196,3229,3245,3260,3277,3292,3308,3351,3355,3357,3358,3373,3379,3381,3382,3385,3386,3388,3405,3417,3418,3420,3433,3436,3448,3469,3477,3478,3484,3493,3500,3508,3532,3613,3630,3644,3669,3686,3700,3737,3754,3768,3854,3868,3910,3924,3978,3992,4034,4048]
def rows : List LinearRow := [⟨.covers 2055,1,8⟩,⟨.covers 1035,1,8⟩,⟨.covers 1539,1,13⟩,⟨.covers 2563,1,13⟩,⟨.covers 77,1,9⟩,⟨.covers 141,1,8⟩,⟨.covers 149,1,5⟩,⟨.covers 293,1,2⟩,⟨.covers 197,1,2⟩,⟨.covers 89,1,5⟩,⟨.covers 297,1,2⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 526,1,7⟩,⟨.covers 86,1,13⟩,⟨.covers 198,1,17⟩,⟨.covers 154,1,12⟩,⟨.covers 106,1,1⟩,⟨.covers 202,1,19⟩,⟨.covers 210,1,19⟩,⟨.covers 226,1,19⟩,⟨.covers 1570,1,1⟩,⟨.covers 1346,1,1⟩,⟨.covers 212,1,19⟩,⟨.covers 228,1,19⟩,⟨.covers 804,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 808,1,2⟩,⟨.covers 624,1,1⟩,⟨.covers 688,1,1⟩,⟨.covers 2352,1,2⟩,⟨.covers 1808,1,5⟩,⟨.covers 2832,1,2⟩,⟨.covers 1376,1,12⟩,⟨.covers 2656,1,13⟩,⟨.covers 2464,1,11⟩,⟨.covers 1696,1,12⟩,⟨.covers 2496,1,6⟩,⟨.covers 1920,1,5⟩,⟨.incident 6,8,-6⟩,⟨.incident 7,8,-5⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_008
namespace C13.Global.FastDual53_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,10]
def points : Finset C13.Point := {1,6,7,10}
def columns : List Code := [829,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1639,1646,1654,1693,1709,1721,1870,1882,1894,1906,1933,1945,1957,1969,2173,2238,2365,2397,2413,2425,2455,2462,2486,2621,2653,2669,2677,2731,2734,2746,2845,2861,2869,2873,2876,2893,2901,2905,2917,2921,2929,2951,2955,2958,2963,2966,2970,2979,2982,2986,2994,3011,3127,3131,3229,3245,3277,3292,3308,3355,3379,3418,3469,3493,3532,3623,3635,3686,3725,3737,3788]
def rows : List LinearRow := [⟨.covers 39,1,3⟩,⟨.covers 71,1,5⟩,⟨.covers 43,1,5⟩,⟨.covers 75,1,8⟩,⟨.covers 2307,1,1⟩,⟨.covers 77,1,4⟩,⟨.covers 141,1,2⟩,⟨.covers 525,1,1⟩,⟨.covers 149,1,5⟩,⟨.covers 101,1,4⟩,⟨.covers 197,1,10⟩,⟨.covers 2309,1,1⟩,⟨.covers 89,1,4⟩,⟨.covers 169,1,2⟩,⟨.covers 297,1,3⟩,⟨.covers 142,1,3⟩,⟨.covers 526,1,3⟩,⟨.covers 86,1,11⟩,⟨.covers 166,1,2⟩,⟨.covers 3078,1,3⟩,⟨.covers 154,1,4⟩,⟨.covers 106,1,1⟩,⟨.covers 202,1,7⟩,⟨.covers 1546,1,8⟩,⟨.covers 210,1,15⟩,⟨.covers 226,1,15⟩,⟨.covers 2818,1,2⟩,⟨.covers 3330,1,4⟩,⟨.covers 212,1,15⟩,⟨.covers 596,1,1⟩,⟨.covers 404,1,2⟩,⟨.covers 2580,1,3⟩,⟨.covers 228,1,10⟩,⟨.covers 1316,1,2⟩,⟨.covers 3332,1,1⟩,⟨.covers 568,1,2⟩,⟨.covers 1560,1,1⟩,⟨.covers 360,1,1⟩,⟨.covers 680,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 2384,1,4⟩,⟨.covers 2704,1,2⟩,⟨.covers 1808,1,1⟩,⟨.covers 3600,1,5⟩,⟨.covers 1376,1,10⟩,⟨.covers 2656,1,4⟩,⟨.covers 3168,1,6⟩,⟨.covers 2464,1,5⟩,⟨.covers 1696,1,2⟩,⟨.covers 1472,1,1⟩,⟨.covers 2496,1,9⟩,⟨.covers 1728,1,15⟩,⟨.covers 2880,1,4⟩,⟨.covers 3392,1,4⟩,⟨.covers 1920,1,5⟩,⟨.incident 6,8,-7⟩,⟨.incident 7,8,-3⟩]
def bound : Int := 6

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_009
namespace C13.Global.FastDual53_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,9,10]
def points : Finset C13.Point := {1,6,9,10}
def columns : List Code := [445,475,701,743,829,925,953,956,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1465,1498,1639,1646,1654,1693,1721,1766,1894,1945,2173,2231,2235,2237,2238,2269,2285,2365,2397,2413,2425,2455,2459,2461,2462,2477,2483,2485,2486,2489,2490,2492,2509,2521,2537,2621,2653,2677,2717,2731,2734,2745,2746,2748,2773,2845,2876,2901,2955,2969,2986,3000,3011,3025,3127,3131,3229,3245,3251,3253,3257,3277,3292,3308,3355,3379,3418,3469,3481,3493,3505,3532,3544,3686,3737]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 43,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 1283,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 86,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 360,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 624,1,1⟩,⟨.covers 688,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 2608,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 848,1,1⟩,⟨.covers 3152,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 3392,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_010
namespace C13.Global.FastDual53_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,9,11]
def points : Finset C13.Point := {1,6,9,11}
def columns : List Code := [445,475,701,743,829,925,953,956,967,971,979,995,1150,1213,1341,1371,1374,1402,1437,1453,1461,1465,1468,1498,1597,1639,1646,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2173,2231,2235,2238,2269,2285,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2653,2677,2731,2734,2746,2773,2901,2986,3127,3131,3165,3181,3251,3254,3258,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 135,1,2⟩,⟨.covers 1031,1,2⟩,⟨.covers 2055,1,1⟩,⟨.covers 1035,1,2⟩,⟨.covers 147,1,1⟩,⟨.covers 1059,1,1⟩,⟨.covers 2307,1,1⟩,⟨.covers 1539,1,12⟩,⟨.covers 2563,1,18⟩,⟨.covers 525,1,5⟩,⟨.covers 201,1,1⟩,⟨.covers 777,1,5⟩,⟨.covers 3081,1,3⟩,⟨.covers 1169,1,2⟩,⟨.covers 1665,1,3⟩,⟨.covers 78,1,2⟩,⟨.covers 526,1,5⟩,⟨.covers 198,1,10⟩,⟨.covers 390,1,2⟩,⟨.covers 774,1,1⟩,⟨.covers 3078,1,2⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,3⟩,⟨.covers 226,1,4⟩,⟨.covers 2818,1,17⟩,⟨.covers 3586,1,16⟩,⟨.covers 300,1,2⟩,⟨.covers 2316,1,3⟩,⟨.covers 1548,1,5⟩,⟨.covers 2572,1,13⟩,⟨.covers 804,1,3⟩,⟨.covers 1220,1,2⟩,⟨.covers 2820,1,18⟩,⟨.covers 3588,1,12⟩,⟨.covers 232,1,1⟩,⟨.covers 624,1,4⟩,⟨.covers 2160,1,1⟩,⟨.covers 688,1,5⟩,⟨.covers 2352,1,4⟩,⟨.covers 1584,1,5⟩,⟨.covers 2608,1,13⟩,⟨.covers 1232,1,2⟩,⟨.covers 1616,1,6⟩,⟨.covers 912,1,5⟩,⟨.covers 3216,1,2⟩,⟨.covers 864,1,11⟩,⟨.covers 3168,1,3⟩,⟨.covers 2496,1,1⟩,⟨.covers 2752,1,18⟩,⟨.incident 9,8,-13⟩,⟨.incident 11,8,-3⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_011
namespace C13.Global.FastDual53_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,10,11]
def points : Finset C13.Point := {1,6,10,11}
def columns : List Code := [445,475,701,743,829,925,941,949,953,956,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1465,1498,1639,1646,1654,1693,1709,1717,1721,1766,1870,1882,1894,1906,1933,1945,1957,1969,2173,2231,2235,2238,2269,2285,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2653,2669,2677,2731,2734,2739,2742,2746,2765,2773,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3251,3277,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 1031,1,7⟩,⟨.covers 2055,1,2⟩,⟨.covers 523,1,3⟩,⟨.covers 1037,1,5⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,5⟩,⟨.covers 3077,1,9⟩,⟨.covers 89,1,1⟩,⟨.covers 537,1,3⟩,⟨.covers 1289,1,5⟩,⟨.covers 2569,1,2⟩,⟨.covers 3081,1,4⟩,⟨.covers 142,1,3⟩,⟨.covers 86,1,12⟩,⟨.covers 1286,1,2⟩,⟨.covers 2566,1,2⟩,⟨.covers 154,1,2⟩,⟨.covers 554,1,2⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,12⟩,⟨.covers 3082,1,14⟩,⟨.covers 114,1,2⟩,⟨.covers 3330,1,18⟩,⟨.covers 3586,1,18⟩,⟨.covers 2580,1,1⟩,⟨.covers 420,1,3⟩,⟨.covers 1316,1,2⟩,⟨.covers 3332,1,18⟩,⟨.covers 3588,1,18⟩,⟨.covers 1560,1,2⟩,⟨.covers 232,1,1⟩,⟨.covers 360,1,2⟩,⟨.covers 2160,1,3⟩,⟨.covers 1200,1,5⟩,⟨.covers 720,1,3⟩,⟨.covers 1232,1,7⟩,⟨.covers 2384,1,1⟩,⟨.covers 3152,1,10⟩,⟨.covers 1424,1,5⟩,⟨.covers 2704,1,3⟩,⟨.covers 1248,1,9⟩,⟨.covers 1376,1,10⟩,⟨.covers 2656,1,2⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,5⟩,⟨.covers 3232,1,7⟩,⟨.incident 10,8,-11⟩,⟨.incident 11,8,-4⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_012
namespace C13.Global.FastDual53_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,7]
def points : Finset C13.Point := {2,3,6,7}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,979,995,1371,1402,1447,1461,1639,1654,1691,1721,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1955,1957,1969,1987,2411,2425,2455,2486,2647,2677,2731,2746,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2966,2979,2986,2994,3011,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3477,3478,3493,3494,3508,3532,3635,3655,3669,3670,3685,3686,3700,3723,3737,3738,3753,3754,3768,3788,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 135,1,5⟩,⟨.covers 1031,1,7⟩,⟨.covers 2055,1,1⟩,⟨.covers 75,1,4⟩,⟨.covers 139,1,2⟩,⟨.covers 1035,1,9⟩,⟨.covers 2059,1,1⟩,⟨.covers 45,1,19⟩,⟨.covers 77,1,19⟩,⟨.covers 149,1,7⟩,⟨.covers 101,1,5⟩,⟨.covers 2309,1,1⟩,⟨.covers 1541,1,3⟩,⟨.covers 89,1,3⟩,⟨.covers 169,1,12⟩,⟨.covers 1289,1,2⟩,⟨.covers 2569,1,2⟩,⟨.covers 3089,1,9⟩,⟨.covers 2369,1,4⟩,⟨.covers 2625,1,2⟩,⟨.covers 1409,1,1⟩,⟨.covers 1665,1,1⟩,⟨.covers 46,1,19⟩,⟨.covers 78,1,19⟩,⟨.covers 86,1,11⟩,⟨.covers 166,1,2⟩,⟨.covers 2566,1,2⟩,⟨.covers 154,1,5⟩,⟨.covers 106,1,7⟩,⟨.covers 1546,1,2⟩,⟨.covers 210,1,19⟩,⟨.covers 3090,1,2⟩,⟨.covers 226,1,19⟩,⟨.covers 3106,1,9⟩,⟨.covers 2434,1,4⟩,⟨.covers 1794,1,4⟩,⟨.covers 92,1,19⟩,⟨.covers 108,1,19⟩,⟨.covers 2316,1,9⟩,⟨.covers 1548,1,2⟩,⟨.covers 116,1,1⟩,⟨.covers 180,1,5⟩,⟨.covers 2324,1,1⟩,⟨.covers 2580,1,1⟩,⟨.covers 1316,1,3⟩,⟨.covers 1572,1,1⟩,⟨.covers 1604,1,1⟩,⟨.covers 2628,1,1⟩,⟨.covers 120,1,6⟩,⟨.covers 184,1,1⟩,⟨.covers 1304,1,1⟩,⟨.covers 1560,1,1⟩,⟨.covers 2344,1,4⟩,⟨.covers 2696,1,3⟩,⟨.covers 1136,1,6⟩,⟨.covers 2160,1,3⟩,⟨.covers 1200,1,3⟩,⟨.covers 2224,1,6⟩,⟨.covers 1616,1,1⟩,⟨.covers 2704,1,4⟩,⟨.covers 2832,1,4⟩,⟨.covers 2656,1,6⟩,⟨.covers 2464,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 2496,1,9⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_013
namespace C13.Global.FastDual53_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,9]
def points : Finset C13.Point := {2,3,6,9}
def columns : List Code := [379,439,631,699,829,830,953,954,956,979,995,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1721,1722,1766,1852,1894,1945,1976,1987,2018,2411,2425,2455,2483,2485,2486,2537,2647,2677,2731,2745,2746,2773,2876,2901,2986,3000,3011,3025,3251,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3475,3477,3478,3491,3493,3494,3505,3506,3508,3529,3530,3532,3544,3560,3655,3669,3686,3700,3723,3737,3754,3768,3854,3868,3910,3924,3978,3992,4034,4048]
def rows : List LinearRow := [⟨.covers 135,1,6⟩,⟨.covers 45,1,25⟩,⟨.covers 77,1,25⟩,⟨.covers 149,1,6⟩,⟨.covers 2309,1,6⟩,⟨.covers 1541,1,25⟩,⟨.covers 46,1,25⟩,⟨.covers 78,1,6⟩,⟨.covers 86,1,25⟩,⟨.covers 166,1,6⟩,⟨.covers 198,1,19⟩,⟨.covers 92,1,6⟩,⟨.covers 108,1,6⟩,⟨.covers 172,1,19⟩,⟨.covers 2316,1,6⟩,⟨.covers 180,1,6⟩,⟨.covers 212,1,19⟩,⟨.covers 1316,1,12⟩,⟨.covers 2436,1,6⟩,⟨.covers 2820,1,19⟩,⟨.covers 2656,1,25⟩,⟨.incident 2,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_014
namespace C13.Global.FastDual53_015
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,10]
def points : Finset C13.Point := {2,3,6,10}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1498,1639,1654,1691,1715,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2411,2425,2455,2483,2485,2486,2537,2647,2677,2731,2739,2745,2746,2773,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2965,2966,2979,2985,2986,2993,2994,2996,3000,3011,3025,3041,3251,3277,3278,3292,3308,3379,3418,3493,3505,3532,3544,3635,3686,3737,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 135,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 1541,1,1⟩,⟨.covers 1289,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 1856,1,1⟩,⟨.covers 2880,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_015
