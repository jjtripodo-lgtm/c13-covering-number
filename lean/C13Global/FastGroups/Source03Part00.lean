import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source03
namespace C13.Global.FastDual03_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,7]
def points : Finset C13.Point := {2,3,6,7}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,979,995,1371,1402,1447,1461,1639,1654,1691,1721,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1955,1957,1969,1987,2411,2425,2455,2486,2647,2677,2731,2746,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2966,2979,2986,2994,3011,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3477,3478,3493,3494,3508,3532,3635,3655,3669,3670,3685,3686,3700,3723,3737,3738,3753,3754,3768,3788,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 135,1,3⟩,⟨.covers 2055,1,1⟩,⟨.covers 1035,1,12⟩,⟨.covers 2059,1,12⟩,⟨.covers 77,1,50⟩,⟨.covers 269,1,22⟩,⟨.covers 149,1,7⟩,⟨.covers 101,1,1⟩,⟨.covers 89,1,12⟩,⟨.covers 169,1,22⟩,⟨.covers 1289,1,1⟩,⟨.covers 449,1,1⟩,⟨.covers 897,1,3⟩,⟨.covers 1409,1,1⟩,⟨.covers 78,1,50⟩,⟨.covers 270,1,12⟩,⟨.covers 166,1,3⟩,⟨.covers 1286,1,1⟩,⟨.covers 154,1,18⟩,⟨.covers 106,1,12⟩,⟨.covers 778,1,10⟩,⟨.covers 450,1,1⟩,⟨.covers 898,1,2⟩,⟨.covers 2434,1,2⟩,⟨.covers 92,1,50⟩,⟨.covers 108,1,50⟩,⟨.covers 300,1,8⟩,⟨.covers 1548,1,16⟩,⟨.covers 1604,1,1⟩,⟨.covers 1412,1,5⟩,⟨.covers 120,1,12⟩,⟨.covers 184,1,8⟩,⟨.covers 792,1,9⟩,⟨.covers 1560,1,6⟩,⟨.covers 2344,1,12⟩,⟨.covers 2600,1,2⟩,⟨.covers 1352,1,12⟩,⟨.covers 1672,1,12⟩,⟨.covers 2696,1,12⟩,⟨.covers 2224,1,8⟩,⟨.covers 464,1,5⟩,⟨.covers 480,1,5⟩,⟨.covers 2752,1,3⟩,⟨.covers 1920,1,4⟩,⟨.incident 2,8,-1⟩,⟨.incident 3,8,-38⟩,⟨.incident 7,8,-11⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source03.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source03.rootCodes link03 points rows bound = true := by decide +kernel

end C13.Global.FastDual03_000
namespace C13.Global.FastDual03_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,8]
def points : Finset C13.Point := {2,3,6,8}
def columns : List Code := [379,439,631,699,829,830,949,950,956,979,995,1371,1402,1447,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1852,1882,1957,1972,1987,2002,2411,2425,2455,2485,2486,2537,2647,2677,2731,2739,2745,2746,2773,2876,2921,2966,2996,3011,3041,3251,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3635,3655,3669,3670,3685,3686,3700,3723,3731,3737,3738,3747,3753,3754,3761,3762,3768,3781,3782,3788,3796,3812,3854,3884,3914,3944,3974,4004,4034,4064]
def rows : List LinearRow := [⟨.covers 71,1,5⟩,⟨.covers 139,1,6⟩,⟨.covers 77,1,34⟩,⟨.covers 269,1,9⟩,⟨.covers 101,1,5⟩,⟨.covers 2309,1,6⟩,⟨.covers 1541,1,6⟩,⟨.covers 169,1,3⟩,⟨.covers 1289,1,14⟩,⟨.covers 2569,1,10⟩,⟨.covers 1073,1,6⟩,⟨.covers 705,1,2⟩,⟨.covers 2625,1,1⟩,⟨.covers 78,1,28⟩,⟨.covers 270,1,9⟩,⟨.covers 86,1,7⟩,⟨.covers 166,1,6⟩,⟨.covers 198,1,1⟩,⟨.covers 154,1,9⟩,⟨.covers 106,1,10⟩,⟨.covers 2090,1,4⟩,⟨.covers 202,1,5⟩,⟨.covers 1122,1,4⟩,⟨.covers 3106,1,9⟩,⟨.covers 92,1,31⟩,⟨.covers 156,1,2⟩,⟨.covers 284,1,8⟩,⟨.covers 108,1,15⟩,⟨.covers 1548,1,5⟩,⟨.covers 2572,1,3⟩,⟨.covers 116,1,7⟩,⟨.covers 212,1,1⟩,⟨.covers 2580,1,3⟩,⟨.covers 228,1,9⟩,⟨.covers 1604,1,4⟩,⟨.covers 2628,1,7⟩,⟨.covers 184,1,7⟩,⟨.covers 1560,1,4⟩,⟨.covers 232,1,11⟩,⟨.covers 2600,1,3⟩,⟨.covers 1672,1,6⟩,⟨.covers 848,1,1⟩,⟨.covers 2384,1,14⟩,⟨.covers 1616,1,2⟩,⟨.covers 2704,1,3⟩,⟨.covers 3712,1,3⟩,⟨.incident 2,8,-6⟩,⟨.incident 3,8,-10⟩,⟨.incident 6,8,-3⟩,⟨.incident 8,8,15⟩]
def bound : Int := 16

theorem column_mask : listMask columns = restrictMask universeMask Source03.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source03.rootCodes link03 points rows bound = true := by decide +kernel

end C13.Global.FastDual03_001
namespace C13.Global.FastDual03_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,9]
def points : Finset C13.Point := {2,3,6,9}
def columns : List Code := [379,439,631,699,829,830,953,954,956,979,995,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1721,1722,1766,1852,1894,1945,1976,1987,2018,2411,2425,2455,2483,2485,2486,2537,2647,2677,2731,2745,2746,2773,2876,2901,2986,3000,3011,3025,3251,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3475,3477,3478,3491,3493,3494,3505,3506,3508,3529,3530,3532,3544,3560,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 77,1,7⟩,⟨.covers 269,1,9⟩,⟨.covers 149,1,5⟩,⟨.covers 101,1,9⟩,⟨.covers 1061,1,2⟩,⟨.covers 197,1,9⟩,⟨.covers 773,1,9⟩,⟨.covers 2309,1,5⟩,⟨.covers 1541,1,2⟩,⟨.covers 89,1,1⟩,⟨.covers 1049,1,1⟩,⟨.covers 169,1,2⟩,⟨.covers 201,1,2⟩,⟨.covers 1289,1,3⟩,⟨.covers 2569,1,2⟩,⟨.covers 2145,1,2⟩,⟨.covers 1185,1,2⟩,⟨.covers 78,1,18⟩,⟨.covers 270,1,18⟩,⟨.covers 86,1,2⟩,⟨.covers 2070,1,2⟩,⟨.covers 166,1,5⟩,⟨.covers 1286,1,5⟩,⟨.covers 2566,1,9⟩,⟨.covers 154,1,3⟩,⟨.covers 1050,1,1⟩,⟨.covers 106,1,2⟩,⟨.covers 2314,1,2⟩,⟨.covers 1546,1,1⟩,⟨.covers 2322,1,2⟩,⟨.covers 2594,1,2⟩,⟨.covers 2818,1,2⟩,⟨.covers 92,1,18⟩,⟨.covers 108,1,11⟩,⟨.covers 2316,1,12⟩,⟨.covers 1548,1,9⟩,⟨.covers 2572,1,6⟩,⟨.covers 116,1,2⟩,⟨.covers 180,1,5⟩,⟨.covers 228,1,7⟩,⟨.covers 1796,1,9⟩,⟨.covers 3332,1,5⟩,⟨.covers 3588,1,2⟩,⟨.covers 120,1,3⟩,⟨.covers 184,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 3592,1,3⟩,⟨.covers 1616,1,9⟩,⟨.covers 912,1,2⟩,⟨.covers 736,1,2⟩,⟨.incident 2,8,-11⟩,⟨.incident 3,8,-5⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source03.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source03.rootCodes link03 points rows bound = true := by decide +kernel

end C13.Global.FastDual03_002
namespace C13.Global.FastDual03_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,10]
def points : Finset C13.Point := {2,3,6,10}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1498,1639,1654,1691,1715,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2411,2425,2455,2483,2485,2486,2537,2647,2677,2731,2739,2745,2746,2773,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2965,2966,2979,2985,2986,2993,2994,2996,3000,3011,3025,3041,3251,3277,3278,3292,3308,3379,3418,3493,3505,3532,3544,3635,3686,3737,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 135,1,4⟩,⟨.covers 1031,1,3⟩,⟨.covers 139,1,4⟩,⟨.covers 1035,1,3⟩,⟨.covers 269,1,11⟩,⟨.covers 2309,1,5⟩,⟨.covers 1541,1,8⟩,⟨.covers 3077,1,6⟩,⟨.covers 1289,1,8⟩,⟨.covers 2569,1,5⟩,⟨.covers 3081,1,5⟩,⟨.covers 78,1,4⟩,⟨.covers 270,1,11⟩,⟨.covers 86,1,11⟩,⟨.covers 166,1,4⟩,⟨.covers 198,1,7⟩,⟨.covers 154,1,4⟩,⟨.covers 106,1,11⟩,⟨.covers 2434,1,2⟩,⟨.covers 2690,1,2⟩,⟨.covers 3330,1,11⟩,⟨.covers 3586,1,11⟩,⟨.covers 92,1,3⟩,⟨.covers 108,1,6⟩,⟨.covers 172,1,5⟩,⟨.covers 1292,1,11⟩,⟨.covers 1548,1,10⟩,⟨.covers 180,1,3⟩,⟨.covers 212,1,7⟩,⟨.covers 2820,1,5⟩,⟨.covers 184,1,3⟩,⟨.covers 2824,1,5⟩,⟨.covers 2160,1,11⟩,⟨.covers 1200,1,8⟩,⟨.covers 2224,1,2⟩,⟨.covers 464,1,7⟩,⟨.covers 720,1,3⟩,⟨.covers 480,1,10⟩,⟨.covers 1856,1,11⟩,⟨.covers 1920,1,3⟩,⟨.covers 3712,1,1⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source03.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source03.rootCodes link03 points rows bound = true := by decide +kernel

end C13.Global.FastDual03_003
namespace C13.Global.FastDual03_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,11]
def points : Finset C13.Point := {2,3,6,11}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1946,1955,1957,1958,1969,1970,1972,1976,1987,2002,2018,2411,2425,2455,2483,2486,2537,2647,2677,2731,2739,2746,2773,2839,2859,2867,2901,2921,2929,2966,2986,2994,3251,3277,3278,3292,3308,3379,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 135,1,3⟩,⟨.covers 2055,1,8⟩,⟨.covers 1035,1,3⟩,⟨.covers 2059,1,8⟩,⟨.covers 269,1,11⟩,⟨.covers 101,1,6⟩,⟨.covers 1541,1,3⟩,⟨.covers 3077,1,6⟩,⟨.covers 89,1,8⟩,⟨.covers 169,1,3⟩,⟨.covers 3081,1,6⟩,⟨.covers 1169,1,3⟩,⟨.covers 3105,1,3⟩,⟨.covers 705,1,3⟩,⟨.covers 1409,1,3⟩,⟨.covers 78,1,11⟩,⟨.covers 270,1,11⟩,⟨.covers 166,1,3⟩,⟨.covers 1286,1,3⟩,⟨.covers 154,1,3⟩,⟨.covers 2314,1,3⟩,⟨.covers 1546,1,3⟩,⟨.covers 3330,1,8⟩,⟨.covers 3586,1,8⟩,⟨.covers 92,1,11⟩,⟨.covers 108,1,11⟩,⟨.covers 116,1,3⟩,⟨.covers 180,1,6⟩,⟨.covers 1796,1,6⟩,⟨.covers 2820,1,3⟩,⟨.covers 3588,1,3⟩,⟨.covers 120,1,3⟩,⟨.covers 184,1,6⟩,⟨.covers 1800,1,6⟩,⟨.covers 3336,1,3⟩,⟨.covers 1136,1,8⟩,⟨.covers 2224,1,3⟩,⟨.covers 464,1,8⟩,⟨.covers 736,1,8⟩,⟨.covers 2656,1,3⟩,⟨.covers 2496,1,8⟩,⟨.covers 2752,1,8⟩,⟨.covers 1856,1,3⟩,⟨.covers 2880,1,8⟩,⟨.covers 2944,1,8⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source03.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source03.rootCodes link03 points rows bound = true := by decide +kernel

end C13.Global.FastDual03_004
namespace C13.Global.FastDual03_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,8,9]
def points : Finset C13.Point := {2,3,8,9}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,829,830,892,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1401,1402,1447,1461,1462,1491,1498,1507,1509,1521,1522,1524,1528,1639,1653,1654,1691,1721,1722,1747,1753,1763,1766,1777,1778,1780,1784,1852,1987,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2425,2426,2455,2485,2486,2515,2518,2531,2537,2545,2546,2548,2552,2647,2677,2678,2731,2745,2746,2771,2773,2787,2794,2801,2802,2804,2808,2876,3011,3056,3187,3251,3271,3275,3277,3278,3283,3285,3286,3289,3290,3292,3299,3301,3302,3305,3306,3308,3313,3314,3316,3320,3403,3418,3433,3448,3463,3478,3493,3508,3523,3538,3553,3568,3655,3669,3686,3700,3723,3737,3754,3768,3779,3793,3810,3824]
def rows : List LinearRow := [⟨.covers 135,1,5⟩,⟨.covers 263,1,1⟩,⟨.covers 519,1,7⟩,⟨.covers 75,1,1⟩,⟨.covers 267,1,9⟩,⟨.covers 523,1,5⟩,⟨.covers 269,1,20⟩,⟨.covers 1037,1,20⟩,⟨.covers 149,1,6⟩,⟨.covers 2309,1,1⟩,⟨.covers 1541,1,7⟩,⟨.covers 89,1,4⟩,⟨.covers 169,1,2⟩,⟨.covers 1289,1,1⟩,⟨.covers 2569,1,8⟩,⟨.covers 1073,1,5⟩,⟨.covers 2097,1,5⟩,⟨.covers 593,1,2⟩,⟨.covers 657,1,2⟩,⟨.covers 353,1,3⟩,⟨.covers 417,1,2⟩,⟨.covers 1313,1,1⟩,⟨.covers 270,1,20⟩,⟨.covers 1038,1,20⟩,⟨.covers 86,1,3⟩,⟨.covers 166,1,3⟩,⟨.covers 1286,1,4⟩,⟨.covers 2566,1,2⟩,⟨.covers 154,1,7⟩,⟨.covers 2314,1,4⟩,⟨.covers 1546,1,2⟩,⟨.covers 1074,1,5⟩,⟨.covers 2098,1,5⟩,⟨.covers 338,1,2⟩,⟨.covers 1298,1,2⟩,⟨.covers 2322,1,2⟩,⟨.covers 610,1,5⟩,⟨.covers 674,1,3⟩,⟨.covers 1794,1,20⟩,⟨.covers 2818,1,20⟩,⟨.covers 172,1,7⟩,⟨.covers 1292,1,20⟩,⟨.covers 2316,1,20⟩,⟨.covers 596,1,2⟩,⟨.covers 2132,1,2⟩,⟨.covers 404,1,2⟩,⟨.covers 2196,1,2⟩,⟨.covers 1124,1,1⟩,⟨.covers 1188,1,4⟩,⟨.covers 3332,1,8⟩,⟨.covers 3588,1,3⟩,⟨.covers 1112,1,1⟩,⟨.covers 1176,1,4⟩,⟨.covers 2152,1,3⟩,⟨.covers 2216,1,1⟩,⟨.covers 3336,1,5⟩,⟨.covers 3592,1,5⟩,⟨.covers 1232,1,4⟩,⟨.covers 2256,1,1⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,2⟩,⟨.covers 912,1,9⟩,⟨.covers 2704,1,1⟩,⟨.covers 2272,1,3⟩,⟨.covers 1376,1,4⟩,⟨.covers 2464,1,1⟩,⟨.covers 3360,1,2⟩,⟨.covers 3616,1,9⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source03.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source03.rootCodes link03 points rows bound = true := by decide +kernel

end C13.Global.FastDual03_005
namespace C13.Global.FastDual03_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,10,11]
def points : Finset C13.Point := {2,3,10,11}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,823,827,829,830,883,885,886,889,890,892,947,949,950,953,954,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1395,1402,1447,1459,1461,1497,1498,1509,1510,1521,1522,1524,1528,1639,1651,1654,1691,1715,1721,1753,1754,1765,1766,1777,1778,1780,1784,1819,1831,1843,1882,1894,1906,1945,1957,1969,2008,2020,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2419,2425,2455,2483,2486,2517,2518,2537,2538,2545,2546,2548,2552,2647,2675,2677,2731,2739,2746,2773,2774,2793,2794,2801,2802,2804,2808,2839,2859,2867,2901,2921,2929,2966,2986,2994,3028,3048,3056,3187,3251,3277,3278,3292,3308,3313,3314,3316,3320,3379,3532,3568,3635,3788,3824]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 269,1,2⟩,⟨.covers 1037,1,2⟩,⟨.covers 2309,1,1⟩,⟨.covers 1541,1,1⟩,⟨.covers 1289,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 270,1,2⟩,⟨.covers 1038,1,2⟩,⟨.covers 2566,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 3330,1,2⟩,⟨.covers 3586,1,2⟩,⟨.covers 108,1,1⟩,⟨.covers 1292,1,2⟩,⟨.covers 1548,1,2⟩,⟨.covers 3216,1,1⟩,⟨.covers 1856,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source03.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source03.rootCodes link03 points rows bound = true := by decide +kernel

end C13.Global.FastDual03_006
namespace C13.Global.FastDual03_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,8,9]
def points : Finset C13.Point := {2,6,8,9}
def columns : List Code := [379,439,445,446,475,491,631,699,829,830,956,971,979,995,1211,1262,1371,1387,1402,1447,1453,1461,1462,1468,1483,1498,1639,1646,1654,1691,1707,1721,1722,1766,1852,1987,2235,2269,2395,2411,2425,2455,2462,2485,2486,2492,2507,2537,2647,2653,2677,2715,2731,2745,2746,2773,2876,3011,3131,3227,3243,3251,3257,3258,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,6⟩,⟨.covers 75,1,1⟩,⟨.covers 523,1,1⟩,⟨.covers 1043,1,2⟩,⟨.covers 2083,1,1⟩,⟨.covers 1037,1,7⟩,⟨.covers 149,1,3⟩,⟨.covers 101,1,7⟩,⟨.covers 773,1,14⟩,⟨.covers 2309,1,3⟩,⟨.covers 89,1,3⟩,⟨.covers 1049,1,1⟩,⟨.covers 1289,1,5⟩,⟨.covers 2569,1,3⟩,⟨.covers 1073,1,1⟩,⟨.covers 1169,1,1⟩,⟨.covers 1313,1,2⟩,⟨.covers 2337,1,2⟩,⟨.covers 2062,1,7⟩,⟨.covers 166,1,3⟩,⟨.covers 774,1,14⟩,⟨.covers 1286,1,3⟩,⟨.covers 2566,1,7⟩,⟨.covers 106,1,3⟩,⟨.covers 2090,1,1⟩,⟨.covers 2314,1,5⟩,⟨.covers 1546,1,2⟩,⟨.covers 2098,1,2⟩,⟨.covers 1298,1,2⟩,⟨.covers 2322,1,2⟩,⟨.covers 2210,1,1⟩,⟨.covers 1794,1,14⟩,⟨.covers 2818,1,12⟩,⟨.covers 1548,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 1796,1,12⟩,⟨.covers 2820,1,14⟩,⟨.covers 3332,1,3⟩,⟨.covers 120,1,6⟩,⟨.covers 184,1,1⟩,⟨.covers 3336,1,3⟩,⟨.covers 1232,1,7⟩,⟨.covers 848,1,2⟩,⟨.covers 2384,1,3⟩,⟨.covers 1616,1,7⟩,⟨.covers 912,1,12⟩,⟨.covers 1424,1,5⟩,⟨.covers 2704,1,2⟩,⟨.covers 2272,1,7⟩,⟨.covers 864,1,14⟩,⟨.covers 1376,1,3⟩,⟨.covers 2464,1,5⟩,⟨.covers 1696,1,3⟩,⟨.covers 2752,1,1⟩,⟨.incident 8,8,-7⟩]
def bound : Int := 8

theorem column_mask : listMask columns = restrictMask universeMask Source03.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source03.rootCodes link03 points rows bound = true := by decide +kernel

end C13.Global.FastDual03_007
