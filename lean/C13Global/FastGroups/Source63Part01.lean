import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source63
namespace C13.Global.FastDual63_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,5,10,11]
def points : Finset C13.Point := {0,5,10,11}
def columns : List Code := [239,253,478,493,638,702,719,727,731,733,734,750,764,830,862,878,892,926,942,956,967,971,973,974,979,981,982,985,986,988,1004,1199,1207,1246,1269,1374,1447,1453,1461,1486,1498,1500,1509,1630,1646,1654,1679,1691,1693,1742,1753,1754,1756,1766,1780,1870,1882,1894,1933,1945,1957,1996,2008,2020,2159,2171,2270,2297,2411,2413,2425,2462,2510,2518,2524,2537,2639,2647,2653,2718,2734,2746,2766,2773,2774,2780,2794,2808,2893,2901,2921,2958,2966,2986,3020,3028,3048,3119,3127,3131,3187,3251,3278,3292,3313,3379,3532,3599,3635,3788,3824]
def rows : List LinearRow := [⟨.covers 71,1,20⟩,⟨.covers 139,1,21⟩,⟨.covers 83,1,13⟩,⟨.covers 147,1,13⟩,⟨.covers 323,1,19⟩,⟨.covers 387,1,18⟩,⟨.covers 525,1,7⟩,⟨.covers 533,1,8⟩,⟨.covers 293,1,2⟩,⟨.covers 2309,1,24⟩,⟨.covers 537,1,7⟩,⟨.covers 2121,1,1⟩,⟨.covers 1289,1,26⟩,⟨.covers 353,1,2⟩,⟨.covers 705,1,4⟩,⟨.covers 1793,1,15⟩,⟨.covers 2817,1,16⟩,⟨.covers 3329,1,13⟩,⟨.covers 54,1,13⟩,⟨.covers 86,1,8⟩,⟨.covers 166,1,3⟩,⟨.covers 390,1,6⟩,⟨.covers 2182,1,37⟩,⟨.covers 58,1,13⟩,⟨.covers 154,1,8⟩,⟨.covers 106,1,3⟩,⟨.covers 330,1,5⟩,⟨.covers 1098,1,37⟩,⟨.covers 610,1,14⟩,⟨.covers 674,1,13⟩,⟨.covers 1570,1,6⟩,⟨.covers 2594,1,6⟩,⟨.covers 706,1,4⟩,⟨.covers 540,1,6⟩,⟨.covers 556,1,4⟩,⟨.covers 116,1,22⟩,⟨.covers 308,1,24⟩,⟨.covers 404,1,2⟩,⟨.covers 2196,1,37⟩,⟨.covers 1188,1,1⟩,⟨.covers 1604,1,3⟩,⟨.covers 2628,1,4⟩,⟨.covers 3332,1,74⟩,⟨.covers 3588,1,30⟩,⟨.covers 184,1,23⟩,⟨.covers 312,1,23⟩,⟨.covers 344,1,3⟩,⟨.covers 1112,1,37⟩,⟨.covers 1672,1,4⟩,⟨.covers 2696,1,3⟩,⟨.covers 736,1,19⟩,⟨.covers 1376,1,24⟩,⟨.covers 2464,1,26⟩,⟨.covers 1824,1,11⟩,⟨.covers 2848,1,10⟩,⟨.covers 1856,1,8⟩,⟨.covers 3648,1,30⟩,⟨.covers 2944,1,8⟩,⟨.incident 0,8,37⟩,⟨.incident 5,8,24⟩,⟨.incident 10,8,16⟩,⟨.incident 11,8,16⟩]
def bound : Int := 108

theorem column_mask : listMask columns = restrictMask universeMask Source63.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source63.rootCodes link63 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual63_008
namespace C13.Global.FastDual63_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,6,7,10]
def points : Finset C13.Point := {0,6,7,10}
def columns : List Code := [239,719,830,967,971,979,995,1150,1199,1213,1374,1390,1402,1447,1453,1461,1630,1646,1654,1679,1691,1693,1721,1870,1882,1894,1906,1933,1945,1957,1969,2159,2173,2238,2366,2411,2413,2425,2462,2478,2486,2622,2639,2647,2653,2677,2718,2734,2746,2846,2862,2870,2874,2876,2887,2891,2893,2899,2901,2905,2915,2917,2921,2929,2958,2966,2970,2982,2986,2994,3011,3119,3127,3131,3166,3182,3278,3292,3308,3367,3379,3406,3418,3493,3532,3599,3611,3635,3662,3686,3737,3788]
def rows : List LinearRow := [⟨.covers 149,1,2⟩,⟨.covers 201,1,2⟩,⟨.covers 1289,1,2⟩,⟨.covers 209,1,2⟩,⟨.covers 390,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 212,1,2⟩,⟨.covers 2704,1,1⟩,⟨.covers 736,1,2⟩,⟨.covers 1248,1,2⟩,⟨.covers 2464,1,1⟩,⟨.covers 1696,1,2⟩,⟨.covers 1472,1,1⟩,⟨.covers 2752,1,2⟩,⟨.covers 3456,1,1⟩,⟨.incident 7,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source63.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source63.rootCodes link63 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual63_009
namespace C13.Global.FastDual63_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,7]
def points : Finset C13.Point := {2,3,6,7}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,979,995,1371,1402,1447,1461,1639,1654,1691,1721,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1955,1957,1969,1987,2411,2425,2455,2486,2647,2677,2731,2746,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2966,2979,2986,2994,3011,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3477,3478,3493,3494,3508,3532,3635,3655,3669,3670,3685,3686,3700,3723,3737,3738,3753,3754,3768,3788,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 45,1,2⟩,⟨.covers 77,1,2⟩,⟨.covers 149,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 209,1,2⟩,⟨.covers 3089,1,1⟩,⟨.covers 225,1,2⟩,⟨.covers 46,1,2⟩,⟨.covers 78,1,2⟩,⟨.covers 86,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 3106,1,1⟩,⟨.covers 92,1,2⟩,⟨.covers 108,1,2⟩,⟨.covers 2316,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 2496,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source63.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source63.rootCodes link63 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual63_010
namespace C13.Global.FastDual63_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,10]
def points : Finset C13.Point := {2,3,6,10}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1498,1639,1654,1691,1715,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2411,2425,2455,2483,2485,2486,2537,2647,2677,2731,2739,2745,2746,2773,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2965,2966,2979,2985,2986,2993,2994,2996,3000,3011,3025,3041,3251,3277,3278,3292,3308,3379,3418,3493,3505,3532,3544,3635,3686,3737,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 209,1,1⟩,⟨.covers 225,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 86,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 706,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 2384,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 1856,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source63.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source63.rootCodes link63 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual63_011
namespace C13.Global.FastDual63_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,11]
def points : Finset C13.Point := {2,3,6,11}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1946,1955,1957,1958,1969,1970,1972,1976,1987,2002,2018,2411,2425,2455,2483,2486,2537,2647,2677,2731,2739,2746,2773,2839,2859,2867,2901,2921,2929,2966,2986,2994,3251,3277,3278,3292,3308,3379,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 135,1,1⟩,⟨.covers 2055,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 1541,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 209,1,1⟩,⟨.covers 225,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 2224,1,1⟩,⟨.covers 2384,1,1⟩,⟨.covers 736,1,1⟩,⟨.covers 3616,1,1⟩,⟨.covers 1856,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source63.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source63.rootCodes link63 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual63_012
