import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source12
namespace C13.Global.FastDual12_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,7]
def points : Finset C13.Point := {2,3,6,7}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,979,995,1371,1402,1447,1461,1639,1654,1691,1721,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1955,1957,1969,1987,2411,2425,2455,2486,2647,2677,2731,2746,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2966,2979,2986,2994,3011,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3477,3478,3493,3494,3508,3532,3635,3655,3669,3670,3685,3686,3700,3723,3737,3738,3753,3754,3768,3788,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 135,1,6⟩,⟨.covers 75,1,6⟩,⟨.covers 139,1,6⟩,⟨.covers 77,1,33⟩,⟨.covers 149,1,6⟩,⟨.covers 101,1,6⟩,⟨.covers 89,1,6⟩,⟨.covers 169,1,6⟩,⟨.covers 209,1,33⟩,⟨.covers 225,1,33⟩,⟨.covers 2369,1,6⟩,⟨.covers 2625,1,6⟩,⟨.covers 78,1,33⟩,⟨.covers 86,1,6⟩,⟨.covers 166,1,6⟩,⟨.covers 154,1,6⟩,⟨.covers 106,1,6⟩,⟨.covers 2434,1,6⟩,⟨.covers 2690,1,6⟩,⟨.covers 92,1,33⟩,⟨.covers 108,1,33⟩,⟨.covers 1604,1,6⟩,⟨.covers 1412,1,6⟩,⟨.covers 1352,1,6⟩,⟨.covers 1672,1,6⟩,⟨.covers 2160,1,6⟩,⟨.covers 2224,1,6⟩,⟨.covers 1616,1,6⟩,⟨.covers 1424,1,6⟩,⟨.covers 1376,1,6⟩,⟨.covers 1696,1,6⟩,⟨.covers 1728,1,22⟩,⟨.incident 6,8,-17⟩,⟨.incident 7,8,-17⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source12.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source12.rootCodes link12 points rows bound = true := by decide +kernel

end C13.Global.FastDual12_000
namespace C13.Global.FastDual12_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,10]
def points : Finset C13.Point := {2,3,6,10}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1498,1639,1654,1691,1715,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2411,2425,2455,2483,2485,2486,2537,2647,2677,2731,2739,2745,2746,2773,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2965,2966,2979,2985,2986,2993,2994,2996,3000,3011,3025,3041,3251,3277,3278,3292,3308,3379,3418,3493,3505,3532,3544,3635,3686,3737,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 2055,1,4⟩,⟨.covers 1035,1,11⟩,⟨.covers 2059,1,4⟩,⟨.covers 269,1,11⟩,⟨.covers 149,1,5⟩,⟨.covers 101,1,8⟩,⟨.covers 3077,1,1⟩,⟨.covers 169,1,5⟩,⟨.covers 201,1,3⟩,⟨.covers 3081,1,6⟩,⟨.covers 78,1,4⟩,⟨.covers 270,1,11⟩,⟨.covers 1286,1,11⟩,⟨.covers 2566,1,4⟩,⟨.covers 106,1,2⟩,⟨.covers 2314,1,4⟩,⟨.covers 3082,1,6⟩,⟨.covers 178,1,1⟩,⟨.covers 210,1,11⟩,⟨.covers 2194,1,2⟩,⟨.covers 226,1,11⟩,⟨.covers 2210,1,2⟩,⟨.covers 3106,1,1⟩,⟨.covers 92,1,5⟩,⟨.covers 108,1,8⟩,⟨.covers 1292,1,11⟩,⟨.covers 1548,1,5⟩,⟨.covers 2572,1,6⟩,⟨.covers 180,1,5⟩,⟨.covers 212,1,6⟩,⟨.covers 2820,1,2⟩,⟨.covers 120,1,8⟩,⟨.covers 184,1,5⟩,⟨.covers 232,1,3⟩,⟨.covers 2824,1,2⟩,⟨.covers 2160,1,2⟩,⟨.covers 2224,1,1⟩,⟨.covers 1616,1,11⟩,⟨.covers 3600,1,4⟩,⟨.covers 3360,1,10⟩,⟨.covers 3616,1,6⟩,⟨.covers 2880,1,8⟩,⟨.covers 1920,1,11⟩,⟨.covers 2944,1,2⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source12.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source12.rootCodes link12 points rows bound = true := by decide +kernel

end C13.Global.FastDual12_001
