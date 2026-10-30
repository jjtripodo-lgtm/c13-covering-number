import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source14
namespace C13.Global.FastDual14_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,7]
def points : Finset C13.Point := {2,3,6,7}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,979,995,1371,1402,1447,1461,1639,1654,1691,1721,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1955,1957,1969,1987,2411,2425,2455,2486,2647,2677,2731,2746,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2966,2979,2986,2994,3011,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3477,3478,3493,3494,3508,3532,3635,3655,3669,3670,3685,3686,3700,3723,3737,3738,3753,3754,3768,3788,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 71,1,12⟩,⟨.covers 75,1,10⟩,⟨.covers 77,1,34⟩,⟨.covers 101,1,9⟩,⟨.covers 89,1,12⟩,⟨.covers 209,1,34⟩,⟨.covers 2129,1,2⟩,⟨.covers 225,1,34⟩,⟨.covers 2369,1,12⟩,⟨.covers 2625,1,4⟩,⟨.covers 78,1,34⟩,⟨.covers 86,1,9⟩,⟨.covers 106,1,12⟩,⟨.covers 1122,1,2⟩,⟨.covers 1346,1,12⟩,⟨.covers 1602,1,4⟩,⟨.covers 92,1,34⟩,⟨.covers 108,1,34⟩,⟨.covers 116,1,5⟩,⟨.covers 1604,1,7⟩,⟨.covers 2628,1,7⟩,⟨.covers 2384,1,8⟩,⟨.covers 1616,1,8⟩,⟨.covers 1376,1,8⟩,⟨.covers 2656,1,8⟩,⟨.covers 1728,1,18⟩,⟨.incident 6,8,-34⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source14.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source14.rootCodes link14 points rows bound = true := by decide +kernel

end C13.Global.FastDual14_000
namespace C13.Global.FastDual14_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,8]
def points : Finset C13.Point := {2,3,6,8}
def columns : List Code := [379,439,631,699,829,830,949,950,956,979,995,1371,1402,1447,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1852,1882,1957,1972,1987,2002,2411,2425,2455,2485,2486,2537,2647,2677,2731,2739,2745,2746,2773,2876,2921,2966,2996,3011,3041,3251,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3635,3655,3669,3670,3685,3686,3700,3723,3731,3737,3738,3747,3753,3754,3761,3762,3768,3781,3782,3788,3796,3812]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 77,1,14⟩,⟨.covers 269,1,6⟩,⟨.covers 149,1,2⟩,⟨.covers 2069,1,2⟩,⟨.covers 101,1,2⟩,⟨.covers 1061,1,2⟩,⟨.covers 2309,1,1⟩,⟨.covers 1541,1,4⟩,⟨.covers 89,1,12⟩,⟨.covers 169,1,3⟩,⟨.covers 201,1,3⟩,⟨.covers 777,1,9⟩,⟨.covers 2569,1,3⟩,⟨.covers 209,1,6⟩,⟨.covers 1169,1,2⟩,⟨.covers 1553,1,2⟩,⟨.covers 78,1,11⟩,⟨.covers 270,1,3⟩,⟨.covers 86,1,2⟩,⟨.covers 2070,1,2⟩,⟨.covers 166,1,2⟩,⟨.covers 774,1,2⟩,⟨.covers 1286,1,3⟩,⟨.covers 2566,1,4⟩,⟨.covers 154,1,3⟩,⟨.covers 202,1,6⟩,⟨.covers 778,1,9⟩,⟨.covers 2314,1,12⟩,⟨.covers 1546,1,3⟩,⟨.covers 226,1,6⟩,⟨.covers 1122,1,2⟩,⟨.covers 2210,1,2⟩,⟨.covers 2594,1,2⟩,⟨.covers 92,1,8⟩,⟨.covers 156,1,9⟩,⟨.covers 108,1,17⟩,⟨.covers 1292,1,3⟩,⟨.covers 2316,1,15⟩,⟨.covers 1548,1,11⟩,⟨.covers 116,1,6⟩,⟨.covers 180,1,2⟩,⟨.covers 3332,1,3⟩,⟨.covers 3588,1,2⟩,⟨.covers 184,1,3⟩,⟨.covers 3592,1,3⟩,⟨.covers 1376,1,10⟩,⟨.covers 3360,1,2⟩,⟨.covers 1472,1,3⟩,⟨.covers 2496,1,6⟩,⟨.covers 1920,1,2⟩,⟨.incident 2,8,-5⟩,⟨.incident 3,8,-6⟩,⟨.incident 6,8,-2⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source14.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source14.rootCodes link14 points rows bound = true := by decide +kernel

end C13.Global.FastDual14_001
