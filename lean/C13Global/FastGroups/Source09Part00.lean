import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source09
namespace C13.Global.FastDual09_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,7]
def points : Finset C13.Point := {2,3,6,7}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,979,995,1371,1402,1447,1461,1639,1654,1691,1721,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1955,1957,1969,1987,2411,2425,2455,2486,2647,2677,2731,2746,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2966,2979,2986,2994,3011,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3477,3478,3493,3494,3508,3532,3635,3655,3669,3670,3685,3686,3700,3723,3737,3738,3753,3754,3768,3788,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 135,1,6⟩,⟨.covers 75,1,6⟩,⟨.covers 139,1,6⟩,⟨.covers 77,1,33⟩,⟨.covers 149,1,6⟩,⟨.covers 101,1,6⟩,⟨.covers 89,1,6⟩,⟨.covers 169,1,6⟩,⟨.covers 2369,1,6⟩,⟨.covers 2625,1,6⟩,⟨.covers 78,1,33⟩,⟨.covers 86,1,6⟩,⟨.covers 166,1,6⟩,⟨.covers 154,1,6⟩,⟨.covers 106,1,6⟩,⟨.covers 210,1,33⟩,⟨.covers 226,1,33⟩,⟨.covers 2434,1,6⟩,⟨.covers 2690,1,6⟩,⟨.covers 92,1,33⟩,⟨.covers 108,1,33⟩,⟨.covers 1604,1,6⟩,⟨.covers 1412,1,6⟩,⟨.covers 1352,1,6⟩,⟨.covers 1672,1,6⟩,⟨.covers 2160,1,6⟩,⟨.covers 2224,1,6⟩,⟨.covers 1616,1,6⟩,⟨.covers 1424,1,6⟩,⟨.covers 1376,1,6⟩,⟨.covers 1696,1,6⟩,⟨.covers 1472,1,22⟩,⟨.incident 6,8,-17⟩,⟨.incident 7,8,-17⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_000
namespace C13.Global.FastDual09_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,8]
def points : Finset C13.Point := {2,3,6,8}
def columns : List Code := [254,379,439,506,631,699,758,829,830,949,950,956,979,995,1010,1371,1402,1447,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1852,1882,1957,1972,1987,2002,2300,2411,2425,2455,2485,2486,2537,2552,2647,2677,2731,2739,2745,2746,2773,2804,2876,2921,2966,2996,3011,3041,3056,3251,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3635,3655,3669,3670,3685,3686,3700,3723,3731,3737,3738,3747,3753,3754,3761,3762,3768,3781,3782,3788,3796,3812]
def rows : List LinearRow := [⟨.covers 77,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 1038,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 1376,1,1⟩,⟨.incident 3,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_001
namespace C13.Global.FastDual09_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,11]
def points : Finset C13.Point := {2,3,6,11}
def columns : List Code := [254,379,439,506,631,699,758,823,827,829,830,883,947,949,950,953,954,956,979,995,1010,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1946,1955,1957,1958,1969,1970,1972,1976,1987,2002,2018,2300,2411,2425,2455,2483,2486,2537,2552,2647,2677,2731,2739,2746,2773,2804,2839,2859,2867,2901,2921,2929,2966,2986,2994,3056,3251,3277,3278,3292,3308,3379,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 135,1,4⟩,⟨.covers 1031,1,4⟩,⟨.covers 139,1,5⟩,⟨.covers 1035,1,2⟩,⟨.covers 77,1,17⟩,⟨.covers 269,1,17⟩,⟨.covers 149,1,10⟩,⟨.covers 101,1,6⟩,⟨.covers 89,1,12⟩,⟨.covers 169,1,9⟩,⟨.covers 705,1,4⟩,⟨.covers 2369,1,1⟩,⟨.covers 1665,1,3⟩,⟨.covers 270,1,17⟩,⟨.covers 1038,1,17⟩,⟨.covers 1286,1,3⟩,⟨.covers 2566,1,14⟩,⟨.covers 106,1,2⟩,⟨.covers 2314,1,11⟩,⟨.covers 1546,1,3⟩,⟨.covers 210,1,2⟩,⟨.covers 226,1,3⟩,⟨.covers 1122,1,4⟩,⟨.covers 450,1,3⟩,⟨.covers 706,1,2⟩,⟨.covers 156,1,3⟩,⟨.covers 2316,1,17⟩,⟨.covers 2572,1,17⟩,⟨.covers 116,1,7⟩,⟨.covers 1188,1,4⟩,⟨.covers 1796,1,7⟩,⟨.covers 1176,1,2⟩,⟨.covers 1800,1,7⟩,⟨.covers 2824,1,3⟩,⟨.covers 464,1,1⟩,⟨.covers 1616,1,2⟩,⟨.covers 3152,1,12⟩,⟨.covers 1808,1,2⟩,⟨.covers 3344,1,11⟩,⟨.covers 3168,1,13⟩,⟨.covers 3616,1,11⟩,⟨.covers 2880,1,10⟩,⟨.incident 2,8,-3⟩,⟨.incident 3,8,-3⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_002
namespace C13.Global.FastDual09_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,8]
def points : Finset C13.Point := {2,3,7,8}
def columns : List Code := [379,439,631,699,829,830,889,890,892,979,995,1371,1401,1402,1447,1461,1509,1639,1651,1653,1654,1691,1721,1753,1852,1882,1912,1957,1987,2017,2411,2425,2426,2455,2486,2518,2647,2675,2677,2678,2731,2746,2794,2876,2921,2936,2966,3011,3026,3187,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3635,3655,3667,3669,3670,3683,3685,3686,3697,3698,3700,3723,3737,3738,3753,3754,3768,3785,3786,3788,3800,3816]
def rows : List LinearRow := [⟨.covers 77,1,16⟩,⟨.covers 269,1,16⟩,⟨.covers 149,1,11⟩,⟨.covers 2069,1,2⟩,⟨.covers 101,1,5⟩,⟨.covers 1541,1,5⟩,⟨.covers 89,1,3⟩,⟨.covers 1049,1,1⟩,⟨.covers 169,1,2⟩,⟨.covers 201,1,2⟩,⟨.covers 777,1,2⟩,⟨.covers 1289,1,1⟩,⟨.covers 2569,1,2⟩,⟨.covers 2577,1,2⟩,⟨.covers 2337,1,2⟩,⟨.covers 78,1,18⟩,⟨.covers 270,1,9⟩,⟨.covers 86,1,5⟩,⟨.covers 1062,1,2⟩,⟨.covers 774,1,9⟩,⟨.covers 1286,1,11⟩,⟨.covers 2566,1,5⟩,⟨.covers 154,1,1⟩,⟨.covers 1050,1,1⟩,⟨.covers 106,1,2⟩,⟨.covers 2314,1,2⟩,⟨.covers 1546,1,3⟩,⟨.covers 210,1,2⟩,⟨.covers 226,1,2⟩,⟨.covers 1122,1,2⟩,⟨.covers 2210,1,2⟩,⟨.covers 92,1,12⟩,⟨.covers 172,1,11⟩,⟨.covers 1292,1,7⟩,⟨.covers 2316,1,18⟩,⟨.covers 116,1,5⟩,⟨.covers 212,1,6⟩,⟨.covers 228,1,7⟩,⟨.covers 1796,1,9⟩,⟨.covers 3588,1,5⟩,⟨.covers 120,1,1⟩,⟨.covers 184,1,3⟩,⟨.covers 1800,1,2⟩,⟨.covers 3336,1,3⟩,⟨.covers 3592,1,1⟩,⟨.covers 1424,1,2⟩,⟨.covers 2464,1,11⟩,⟨.covers 1472,1,2⟩,⟨.incident 2,8,-11⟩,⟨.incident 3,8,-5⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_003
namespace C13.Global.FastDual09_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,11]
def points : Finset C13.Point := {2,3,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,883,885,886,889,890,892,947,979,995,1371,1395,1401,1402,1447,1461,1509,1639,1651,1653,1654,1691,1721,1753,1819,1831,1843,1845,1846,1849,1850,1852,1875,1881,1882,1891,1893,1894,1905,1906,1908,1912,1939,1945,1955,1957,1969,1987,2001,2017,2411,2419,2425,2455,2486,2518,2647,2675,2677,2731,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3187,3277,3278,3292,3308,3379,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 1031,1,4⟩,⟨.covers 2055,1,2⟩,⟨.covers 139,1,4⟩,⟨.covers 1035,1,3⟩,⟨.covers 2059,1,2⟩,⟨.covers 77,1,3⟩,⟨.covers 269,1,11⟩,⟨.covers 149,1,7⟩,⟨.covers 101,1,4⟩,⟨.covers 2309,1,1⟩,⟨.covers 3077,1,4⟩,⟨.covers 89,1,4⟩,⟨.covers 169,1,3⟩,⟨.covers 1289,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 3081,1,3⟩,⟨.covers 78,1,11⟩,⟨.covers 270,1,11⟩,⟨.covers 86,1,1⟩,⟨.covers 166,1,3⟩,⟨.covers 1286,1,3⟩,⟨.covers 2566,1,7⟩,⟨.covers 106,1,1⟩,⟨.covers 2314,1,7⟩,⟨.covers 1546,1,3⟩,⟨.covers 210,1,8⟩,⟨.covers 1106,1,2⟩,⟨.covers 3090,1,1⟩,⟨.covers 226,1,9⟩,⟨.covers 1122,1,2⟩,⟨.covers 156,1,5⟩,⟨.covers 172,1,5⟩,⟨.covers 1292,1,4⟩,⟨.covers 2316,1,6⟩,⟨.covers 2572,1,11⟩,⟨.covers 116,1,5⟩,⟨.covers 212,1,1⟩,⟨.covers 228,1,5⟩,⟨.covers 1796,1,3⟩,⟨.covers 120,1,5⟩,⟨.covers 184,1,3⟩,⟨.covers 216,1,4⟩,⟨.covers 1800,1,3⟩,⟨.covers 2160,1,1⟩,⟨.covers 2224,1,7⟩,⟨.covers 720,1,2⟩,⟨.covers 1424,1,3⟩,⟨.covers 3344,1,3⟩,⟨.covers 3600,1,6⟩,⟨.covers 480,1,1⟩,⟨.covers 1696,1,4⟩,⟨.covers 3360,1,6⟩,⟨.covers 3616,1,3⟩,⟨.covers 1856,1,2⟩,⟨.covers 2880,1,9⟩,⟨.covers 1920,1,3⟩,⟨.covers 2944,1,3⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_004
namespace C13.Global.FastDual09_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,8,9]
def points : Finset C13.Point := {2,3,8,9}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,829,830,892,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1401,1402,1447,1461,1462,1491,1498,1507,1509,1521,1522,1524,1528,1639,1653,1654,1691,1721,1722,1747,1753,1763,1766,1777,1778,1780,1784,1852,1987,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2425,2426,2455,2485,2486,2515,2518,2531,2537,2545,2546,2548,2552,2647,2677,2678,2731,2745,2746,2771,2773,2787,2794,2801,2802,2804,2808,2876,3011,3056,3187,3251,3271,3275,3277,3278,3283,3285,3286,3289,3290,3292,3299,3301,3302,3305,3306,3308,3313,3314,3316,3320,3403,3418,3433,3448,3463,3478,3493,3508,3523,3538,3553,3568,3655,3669,3686,3700,3723,3737,3754,3768,3779,3793,3810,3824]
def rows : List LinearRow := [⟨.covers 267,1,5⟩,⟨.covers 269,1,34⟩,⟨.covers 1037,1,34⟩,⟨.covers 89,1,8⟩,⟨.covers 169,1,8⟩,⟨.covers 2089,1,2⟩,⟨.covers 1289,1,9⟩,⟨.covers 2569,1,12⟩,⟨.covers 270,1,34⟩,⟨.covers 1038,1,34⟩,⟨.covers 154,1,8⟩,⟨.covers 1050,1,2⟩,⟨.covers 106,1,8⟩,⟨.covers 2314,1,9⟩,⟨.covers 1546,1,12⟩,⟨.covers 172,1,18⟩,⟨.covers 1292,1,34⟩,⟨.covers 2316,1,34⟩,⟨.covers 344,1,7⟩,⟨.covers 1112,1,4⟩,⟨.covers 1176,1,12⟩,⟨.covers 360,1,7⟩,⟨.covers 2152,1,4⟩,⟨.covers 2216,1,12⟩,⟨.covers 3336,1,12⟩,⟨.covers 3592,1,10⟩,⟨.incident 3,8,-34⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_005
namespace C13.Global.FastDual09_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,8]
def points : Finset C13.Point := {2,6,7,8}
def columns : List Code := [379,439,631,699,829,830,859,875,971,979,995,1371,1387,1402,1447,1453,1461,1595,1639,1646,1654,1691,1707,1721,1837,1852,1867,1882,1957,1987,2395,2411,2425,2455,2462,2486,2619,2647,2653,2677,2715,2731,2746,2846,2876,2891,2921,2966,3011,3131,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3611,3627,3635,3641,3642,3655,3661,3662,3669,3670,3676,3685,3686,3692,3700,3723,3737,3738,3753,3754,3768,3788]
def rows : List LinearRow := [⟨.covers 1031,1,2⟩,⟨.covers 2055,1,1⟩,⟨.covers 75,1,2⟩,⟨.covers 139,1,3⟩,⟨.covers 141,1,3⟩,⟨.covers 269,1,8⟩,⟨.covers 149,1,14⟩,⟨.covers 101,1,2⟩,⟨.covers 89,1,4⟩,⟨.covers 1049,1,2⟩,⟨.covers 169,1,3⟩,⟨.covers 201,1,9⟩,⟨.covers 2129,1,2⟩,⟨.covers 1553,1,2⟩,⟨.covers 2145,1,2⟩,⟨.covers 2337,1,1⟩,⟨.covers 270,1,8⟩,⟨.covers 86,1,3⟩,⟨.covers 166,1,1⟩,⟨.covers 198,1,12⟩,⟨.covers 1286,1,11⟩,⟨.covers 154,1,3⟩,⟨.covers 106,1,4⟩,⟨.covers 2090,1,2⟩,⟨.covers 210,1,17⟩,⟨.covers 1298,1,2⟩,⟨.covers 226,1,17⟩,⟨.covers 1122,1,2⟩,⟨.covers 2594,1,2⟩,⟨.covers 156,1,3⟩,⟨.covers 116,1,1⟩,⟨.covers 212,1,9⟩,⟨.covers 228,1,12⟩,⟨.covers 3588,1,2⟩,⟨.covers 3336,1,6⟩,⟨.covers 2384,1,2⟩,⟨.covers 1424,1,1⟩,⟨.covers 2704,1,3⟩,⟨.covers 1808,1,8⟩,⟨.covers 1376,1,2⟩,⟨.covers 2464,1,14⟩,⟨.covers 1696,1,3⟩,⟨.covers 2848,1,8⟩,⟨.covers 1472,1,5⟩,⟨.covers 1728,1,1⟩,⟨.covers 2752,1,6⟩,⟨.covers 1920,1,11⟩,⟨.covers 2944,1,11⟩,⟨.covers 3712,1,3⟩,⟨.incident 6,8,-2⟩,⟨.incident 7,8,-6⟩,⟨.incident 8,8,-5⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_006
namespace C13.Global.FastDual09_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,9]
def points : Finset C13.Point := {2,6,7,9}
def columns : List Code := [379,439,631,699,829,830,923,939,971,979,995,1339,1371,1387,1402,1447,1453,1461,1639,1646,1654,1691,1707,1721,1838,1852,1894,1931,1945,1987,2363,2395,2411,2425,2455,2462,2486,2647,2653,2677,2715,2731,2746,2845,2876,2901,2955,2986,3011,3131,3277,3278,3292,3308,3355,3371,3379,3385,3386,3403,3417,3418,3433,3434,3448,3463,3469,3470,3477,3478,3484,3493,3494,3500,3508,3532,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 1031,1,2⟩,⟨.covers 2055,1,1⟩,⟨.covers 75,1,3⟩,⟨.covers 139,1,2⟩,⟨.covers 2083,1,1⟩,⟨.covers 77,1,4⟩,⟨.covers 525,1,6⟩,⟨.covers 149,1,2⟩,⟨.covers 101,1,11⟩,⟨.covers 1061,1,2⟩,⟨.covers 89,1,4⟩,⟨.covers 169,1,4⟩,⟨.covers 201,1,10⟩,⟨.covers 1553,1,3⟩,⟨.covers 2145,1,3⟩,⟨.covers 86,1,3⟩,⟨.covers 166,1,2⟩,⟨.covers 198,1,14⟩,⟨.covers 774,1,6⟩,⟨.covers 2566,1,10⟩,⟨.covers 154,1,3⟩,⟨.covers 1050,1,1⟩,⟨.covers 106,1,3⟩,⟨.covers 210,1,7⟩,⟨.covers 1106,1,1⟩,⟨.covers 2194,1,2⟩,⟨.covers 1298,1,1⟩,⟨.covers 226,1,13⟩,⟨.covers 2594,1,2⟩,⟨.covers 156,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 212,1,13⟩,⟨.covers 228,1,14⟩,⟨.covers 3332,1,2⟩,⟨.covers 3588,1,2⟩,⟨.covers 3592,1,4⟩,⟨.covers 848,1,11⟩,⟨.covers 2384,1,3⟩,⟨.covers 1616,1,10⟩,⟨.covers 1424,1,1⟩,⟨.covers 2704,1,2⟩,⟨.covers 1808,1,6⟩,⟨.covers 864,1,4⟩,⟨.covers 1376,1,4⟩,⟨.covers 2464,1,1⟩,⟨.covers 1696,1,3⟩,⟨.covers 2848,1,6⟩,⟨.covers 1472,1,8⟩,⟨.covers 1728,1,10⟩,⟨.covers 2752,1,18⟩,⟨.covers 3392,1,3⟩,⟨.incident 6,8,-8⟩,⟨.incident 7,8,-4⟩,⟨.incident 9,8,-4⟩]
def bound : Int := 3

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_007
