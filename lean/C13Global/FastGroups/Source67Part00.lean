import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source67
namespace C13.Global.FastDual67_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,2,5,7]
def points : Finset C13.Point := {0,2,5,7}
def columns : List Code := [638,731,830,892,971,979,1447,1453,1461,1509,1646,1654,1691,1753,1838,1846,1852,1882,1894,1900,1908,1931,1939,1945,1957,1987,1993,2001,2171,2270,2411,2425,2462,2518,2647,2651,2653,2654,2682,2746,2778,2794,2846,2874,2876,2891,2899,2901,2902,2905,2906,2908,2921,2922,2936,2966,2970,2986,3011,3018,3026,3131,3187,3278,3292,3371,3379,3385,3418,3427,3433,3441,3470,3478,3484,3493,3526,3532,3540,3611,3635,3642,3662,3667,3669,3670,3673,3674,3676,3686,3690,3698,3737,3738,3754,3786,3788,3800,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 39,1,2⟩,⟨.covers 71,1,2⟩,⟨.covers 1035,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 45,1,2⟩,⟨.covers 77,1,2⟩,⟨.covers 53,1,2⟩,⟨.covers 101,1,2⟩,⟨.covers 201,1,1⟩,⟨.covers 113,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 1038,1,1⟩,⟨.covers 54,1,1⟩,⟨.covers 1346,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 184,1,2⟩,⟨.covers 1304,1,1⟩,⟨.covers 232,1,2⟩,⟨.covers 368,1,1⟩,⟨.covers 464,1,1⟩,⟨.covers 864,1,1⟩,⟨.covers 3232,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source67.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source67.rootCodes link67 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual67_000
namespace C13.Global.FastDual67_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,2,5,9]
def points : Finset C13.Point := {0,2,5,9}
def columns : List Code := [638,731,830,892,956,971,979,985,1447,1453,1461,1498,1509,1646,1654,1691,1747,1753,1766,1838,1852,1894,1908,1931,1945,1987,2001,2171,2270,2411,2425,2462,2518,2522,2524,2537,2647,2653,2746,2771,2773,2777,2794,2876,2901,2986,3000,3011,3025,3131,3187,3251,3278,3286,3290,3292,3371,3379,3385,3418,3427,3433,3441,3470,3478,3482,3484,3491,3493,3497,3505,3526,3530,3532,3538,3540,3544,3553,3669,3686,3737,3754,3793,3810,3847,3861,3878,3892,3971,3985,4002,4016]
def rows : List LinearRow := [⟨.covers 39,1,25⟩,⟨.covers 71,1,25⟩,⟨.covers 45,1,6⟩,⟨.covers 77,1,6⟩,⟨.covers 53,1,6⟩,⟨.covers 149,1,19⟩,⟨.covers 101,1,6⟩,⟨.covers 773,1,25⟩,⟨.covers 142,1,6⟩,⟨.covers 54,1,25⟩,⟨.covers 198,1,6⟩,⟨.covers 156,1,6⟩,⟨.covers 172,1,19⟩,⟨.covers 2316,1,6⟩,⟨.covers 1548,1,25⟩,⟨.covers 2572,1,19⟩,⟨.covers 212,1,6⟩,⟨.covers 228,1,19⟩,⟨.covers 3140,1,6⟩,⟨.covers 2436,1,6⟩,⟨.covers 3204,1,6⟩,⟨.covers 864,1,25⟩,⟨.incident 2,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source67.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source67.rootCodes link67 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual67_001
namespace C13.Global.FastDual67_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,2,5,11]
def points : Finset C13.Point := {0,2,5,11}
def columns : List Code := [638,731,830,892,956,971,979,985,986,1447,1453,1461,1498,1509,1646,1654,1691,1747,1753,1754,1766,1838,1846,1852,1882,1894,1900,1908,1931,1939,1945,1946,1957,1958,1964,1972,1987,1993,1994,2001,2002,2008,2020,2171,2270,2411,2425,2462,2518,2524,2537,2647,2653,2746,2773,2774,2780,2794,2901,2921,2966,2986,3028,3048,3131,3187,3251,3278,3286,3292,3371,3379,3433,3441,3470,3478,3532,3540,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 39,1,16⟩,⟨.covers 71,1,16⟩,⟨.covers 147,1,4⟩,⟨.covers 99,1,4⟩,⟨.covers 2307,1,8⟩,⟨.covers 1539,1,4⟩,⟨.covers 45,1,12⟩,⟨.covers 77,1,6⟩,⟨.covers 53,1,8⟩,⟨.covers 101,1,5⟩,⟨.covers 197,1,11⟩,⟨.covers 773,1,9⟩,⟨.covers 2309,1,7⟩,⟨.covers 3077,1,10⟩,⟨.covers 57,1,8⟩,⟨.covers 169,1,4⟩,⟨.covers 201,1,4⟩,⟨.covers 777,1,4⟩,⟨.covers 2569,1,8⟩,⟨.covers 3081,1,4⟩,⟨.covers 177,1,8⟩,⟨.covers 209,1,4⟩,⟨.covers 1793,1,4⟩,⟨.covers 3585,1,6⟩,⟨.covers 54,1,4⟩,⟨.covers 198,1,5⟩,⟨.covers 1094,1,1⟩,⟨.covers 774,1,2⟩,⟨.covers 3078,1,1⟩,⟨.covers 2322,1,2⟩,⟨.covers 834,1,4⟩,⟨.covers 2818,1,4⟩,⟨.covers 3586,1,2⟩,⟨.covers 156,1,2⟩,⟨.covers 108,1,1⟩,⟨.covers 1100,1,1⟩,⟨.covers 2316,1,4⟩,⟨.covers 1548,1,5⟩,⟨.covers 2572,1,2⟩,⟨.covers 116,1,3⟩,⟨.covers 212,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 3332,1,3⟩,⟨.covers 184,1,4⟩,⟨.covers 312,1,2⟩,⟨.covers 1176,1,4⟩,⟨.covers 232,1,4⟩,⟨.covers 368,1,2⟩,⟨.covers 3344,1,2⟩,⟨.covers 3168,1,8⟩,⟨.covers 1696,1,2⟩,⟨.incident 0,8,-8⟩,⟨.incident 2,8,-4⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source67.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source67.rootCodes link67 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual67_002
namespace C13.Global.FastDual67_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,2,7,9]
def points : Finset C13.Point := {0,2,7,9}
def columns : List Code := [253,501,638,731,761,830,886,892,971,979,995,1009,1402,1447,1453,1461,1509,1646,1654,1660,1691,1721,1753,1838,1852,1894,1908,1931,1945,1987,2001,2171,2270,2300,2411,2419,2425,2426,2462,2486,2518,2548,2647,2653,2677,2678,2684,2746,2794,2808,2876,2901,2932,2986,3011,3042,3056,3131,3187,3193,3194,3278,3292,3308,3371,3379,3385,3386,3418,3427,3433,3434,3441,3442,3448,3470,3478,3484,3493,3494,3500,3508,3526,3532,3540,3556,3669,3686,3700,3737,3754,3768,3847,3861,3878,3892,3971,3985,4002,4016]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 71,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 1728,1,1⟩,⟨.incident 0,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source67.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source67.rootCodes link67 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual67_003
