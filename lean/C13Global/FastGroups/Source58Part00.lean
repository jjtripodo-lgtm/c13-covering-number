import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source58
namespace C13.Global.FastDual58_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,7]
def points : Finset C13.Point := {2,3,6,7}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,979,995,1371,1402,1447,1461,1639,1654,1691,1721,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1955,1957,1969,1987,2411,2425,2455,2486,2647,2677,2731,2746,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2966,2979,2986,2994,3011,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3477,3478,3493,3494,3508,3532,3635,3655,3669,3670,3685,3686,3700,3723,3737,3738,3753,3754,3768,3788,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 71,1,4⟩,⟨.covers 135,1,1⟩,⟨.covers 1031,1,7⟩,⟨.covers 2055,1,2⟩,⟨.covers 75,1,2⟩,⟨.covers 139,1,5⟩,⟨.covers 1035,1,9⟩,⟨.covers 45,1,19⟩,⟨.covers 77,1,19⟩,⟨.covers 149,1,12⟩,⟨.covers 101,1,3⟩,⟨.covers 2309,1,1⟩,⟨.covers 89,1,4⟩,⟨.covers 169,1,7⟩,⟨.covers 1289,1,3⟩,⟨.covers 3089,1,2⟩,⟨.covers 3105,1,9⟩,⟨.covers 2369,1,1⟩,⟨.covers 2625,1,3⟩,⟨.covers 1793,1,4⟩,⟨.covers 2817,1,1⟩,⟨.covers 46,1,19⟩,⟨.covers 78,1,19⟩,⟨.covers 86,1,7⟩,⟨.covers 166,1,5⟩,⟨.covers 1286,1,3⟩,⟨.covers 2566,1,2⟩,⟨.covers 154,1,3⟩,⟨.covers 106,1,11⟩,⟨.covers 2314,1,3⟩,⟨.covers 210,1,19⟩,⟨.covers 3090,1,9⟩,⟨.covers 226,1,19⟩,⟨.covers 1346,1,1⟩,⟨.covers 1602,1,1⟩,⟨.covers 2434,1,1⟩,⟨.covers 2690,1,5⟩,⟨.covers 92,1,19⟩,⟨.covers 108,1,19⟩,⟨.covers 2316,1,7⟩,⟨.covers 2572,1,4⟩,⟨.covers 116,1,5⟩,⟨.covers 180,1,1⟩,⟨.covers 2580,1,1⟩,⟨.covers 1316,1,1⟩,⟨.covers 1572,1,4⟩,⟨.covers 1412,1,2⟩,⟨.covers 2436,1,2⟩,⟨.covers 120,1,2⟩,⟨.covers 184,1,4⟩,⟨.covers 1304,1,1⟩,⟨.covers 1560,1,3⟩,⟨.covers 2344,1,2⟩,⟨.covers 2600,1,2⟩,⟨.covers 1136,1,2⟩,⟨.covers 2160,1,6⟩,⟨.covers 1200,1,3⟩,⟨.covers 2224,1,5⟩,⟨.covers 2384,1,4⟩,⟨.covers 1808,1,1⟩,⟨.covers 2832,1,4⟩,⟨.covers 1376,1,2⟩,⟨.covers 2464,1,4⟩,⟨.covers 1696,1,2⟩,⟨.covers 2496,1,8⟩,⟨.covers 1728,1,3⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source58.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source58.rootCodes link58 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual58_000
namespace C13.Global.FastDual58_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,10]
def points : Finset C13.Point := {2,3,6,10}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1498,1639,1654,1691,1715,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2411,2425,2455,2483,2485,2486,2537,2647,2677,2731,2739,2745,2746,2773,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2965,2966,2979,2985,2986,2993,2994,2996,3000,3011,3025,3041,3251,3277,3278,3292,3308,3379,3418,3493,3505,3532,3544,3635,3686,3737,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 2055,1,5⟩,⟨.covers 1035,1,3⟩,⟨.covers 2059,1,5⟩,⟨.covers 45,1,11⟩,⟨.covers 77,1,3⟩,⟨.covers 149,1,4⟩,⟨.covers 101,1,8⟩,⟨.covers 3077,1,7⟩,⟨.covers 89,1,8⟩,⟨.covers 169,1,4⟩,⟨.covers 3329,1,3⟩,⟨.covers 3585,1,11⟩,⟨.covers 46,1,11⟩,⟨.covers 78,1,11⟩,⟨.covers 1286,1,11⟩,⟨.covers 2566,1,3⟩,⟨.covers 106,1,3⟩,⟨.covers 2314,1,3⟩,⟨.covers 1546,1,8⟩,⟨.covers 178,1,1⟩,⟨.covers 210,1,11⟩,⟨.covers 2194,1,2⟩,⟨.covers 226,1,11⟩,⟨.covers 2210,1,2⟩,⟨.covers 92,1,4⟩,⟨.covers 108,1,11⟩,⟨.covers 1292,1,9⟩,⟨.covers 2316,1,2⟩,⟨.covers 2572,1,3⟩,⟨.covers 180,1,5⟩,⟨.covers 212,1,7⟩,⟨.covers 2820,1,3⟩,⟨.covers 3588,1,7⟩,⟨.covers 184,1,5⟩,⟨.covers 2824,1,3⟩,⟨.covers 1136,1,8⟩,⟨.covers 2160,1,3⟩,⟨.covers 1616,1,3⟩,⟨.covers 3344,1,7⟩,⟨.covers 2880,1,8⟩,⟨.covers 1920,1,11⟩,⟨.covers 2944,1,3⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source58.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source58.rootCodes link58 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual58_001
namespace C13.Global.FastDual58_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,11]
def points : Finset C13.Point := {2,3,6,11}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1946,1955,1957,1958,1969,1970,1972,1976,1987,2002,2018,2411,2425,2455,2483,2486,2537,2647,2677,2731,2739,2746,2773,2839,2859,2867,2901,2921,2929,2966,2986,2994,3251,3277,3278,3292,3308,3379,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 2224,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source58.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source58.rootCodes link58 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual58_002
