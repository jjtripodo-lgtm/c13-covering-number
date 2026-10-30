import C13Global.FastDual
import C13Global.FastMask
import C13Global.Data.Source01
namespace C13.Global.FastDual01_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,7]
def points : Finset C13.Point := {2,3,6,7}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,979,995,1371,1402,1447,1461,1639,1654,1691,1721,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1955,1957,1969,1987,2411,2425,2455,2486,2647,2677,2731,2746,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2966,2979,2986,2994,3011,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3477,3478,3493,3494,3508,3532,3635,3655,3669,3670,3685,3686,3700,3723,3737,3738,3753,3754,3768,3788,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 71,1,10⟩,⟨.covers 135,1,1⟩,⟨.covers 75,1,11⟩,⟨.covers 1035,1,4⟩,⟨.covers 77,1,50⟩,⟨.covers 269,1,3⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,16⟩,⟨.covers 89,1,16⟩,⟨.covers 169,1,4⟩,⟨.covers 449,1,11⟩,⟨.covers 2369,1,5⟩,⟨.covers 2625,1,5⟩,⟨.covers 1409,1,1⟩,⟨.covers 78,1,50⟩,⟨.covers 270,1,3⟩,⟨.covers 86,1,16⟩,⟨.covers 166,1,2⟩,⟨.covers 154,1,3⟩,⟨.covers 106,1,17⟩,⟨.covers 450,1,7⟩,⟨.covers 834,1,4⟩,⟨.covers 1346,1,6⟩,⟨.covers 1602,1,11⟩,⟨.covers 92,1,50⟩,⟨.covers 284,1,2⟩,⟨.covers 108,1,50⟩,⟨.covers 1548,1,2⟩,⟨.covers 1604,1,5⟩,⟨.covers 2628,1,10⟩,⟨.covers 2436,1,2⟩,⟨.covers 120,1,3⟩,⟨.covers 1560,1,1⟩,⟨.covers 2344,1,3⟩,⟨.covers 1352,1,10⟩,⟨.covers 2376,1,10⟩,⟨.covers 2696,1,4⟩,⟨.covers 1136,1,10⟩,⟨.covers 2160,1,5⟩,⟨.covers 688,1,1⟩,⟨.covers 1200,1,2⟩,⟨.covers 464,1,12⟩,⟨.covers 848,1,10⟩,⟨.covers 2384,1,5⟩,⟨.covers 480,1,22⟩,⟨.covers 2656,1,5⟩,⟨.covers 1728,1,5⟩,⟨.covers 2752,1,6⟩,⟨.covers 2880,1,5⟩,⟨.covers 2944,1,1⟩,⟨.incident 3,8,-5⟩,⟨.incident 6,8,-42⟩,⟨.incident 7,8,-3⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source01.alphabets pointList := by
  rw [← fastListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source01.rootCodes link01 points rows bound = true := by decide +kernel

end C13.Global.FastDual01_000
namespace C13.Global.FastDual01_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,8]
def points : Finset C13.Point := {2,3,6,8}
def columns : List Code := [379,439,631,699,829,830,949,950,956,979,995,1371,1402,1447,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1852,1882,1957,1972,1987,2002,2411,2425,2455,2485,2486,2537,2647,2677,2731,2739,2745,2746,2773,2876,2921,2966,2996,3011,3041,3251,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3635,3655,3669,3670,3685,3686,3700,3723,3731,3737,3738,3747,3753,3754,3761,3762,3768,3781,3782,3788,3796,3812]
def rows : List LinearRow := [⟨.covers 77,1,2⟩,⟨.covers 269,1,2⟩,⟨.covers 1289,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 270,1,2⟩,⟨.covers 106,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 92,1,2⟩,⟨.covers 108,1,2⟩,⟨.covers 1292,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 2384,1,1⟩,⟨.incident 2,8,-1⟩,⟨.incident 3,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source01.alphabets pointList := by
  rw [← fastListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source01.rootCodes link01 points rows bound = true := by decide +kernel

end C13.Global.FastDual01_001
namespace C13.Global.FastDual01_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,10]
def points : Finset C13.Point := {2,3,6,10}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1498,1639,1654,1691,1715,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2411,2425,2455,2483,2485,2486,2537,2647,2677,2731,2739,2745,2746,2773,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2965,2966,2979,2985,2986,2993,2994,2996,3000,3011,3025,3041,3251,3277,3278,3292,3308,3379,3418,3493,3505,3532,3544,3635,3686,3737,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 706,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 736,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 2880,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source01.alphabets pointList := by
  rw [← fastListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source01.rootCodes link01 points rows bound = true := by decide +kernel

end C13.Global.FastDual01_002
namespace C13.Global.FastDual01_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,8,9]
def points : Finset C13.Point := {2,3,8,9}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,829,830,892,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1401,1402,1447,1461,1462,1491,1498,1507,1509,1521,1522,1524,1528,1639,1653,1654,1691,1721,1722,1747,1753,1763,1766,1777,1778,1780,1784,1852,1987,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2425,2426,2455,2485,2486,2515,2518,2531,2537,2545,2546,2548,2552,2647,2677,2678,2731,2745,2746,2771,2773,2787,2794,2801,2802,2804,2808,2876,3011,3056,3187,3251,3271,3275,3277,3278,3283,3285,3286,3289,3290,3292,3299,3301,3302,3305,3306,3308,3313,3314,3316,3320,3403,3418,3433,3448,3463,3478,3493,3508,3523,3538,3553,3568,3655,3669,3686,3700,3723,3737,3754,3768,3779,3793,3810,3824]
def rows : List LinearRow := [⟨.covers 267,1,2⟩,⟨.covers 523,1,3⟩,⟨.covers 269,1,34⟩,⟨.covers 1037,1,34⟩,⟨.covers 89,1,13⟩,⟨.covers 169,1,3⟩,⟨.covers 1289,1,8⟩,⟨.covers 2569,1,13⟩,⟨.covers 270,1,34⟩,⟨.covers 1038,1,34⟩,⟨.covers 154,1,3⟩,⟨.covers 1050,1,2⟩,⟨.covers 106,1,13⟩,⟨.covers 2090,1,2⟩,⟨.covers 2314,1,7⟩,⟨.covers 1546,1,12⟩,⟨.covers 92,1,18⟩,⟨.covers 1292,1,34⟩,⟨.covers 2316,1,34⟩,⟨.covers 344,1,2⟩,⟨.covers 1112,1,6⟩,⟨.covers 664,1,5⟩,⟨.covers 1176,1,10⟩,⟨.covers 360,1,4⟩,⟨.covers 2152,1,5⟩,⟨.covers 680,1,3⟩,⟨.covers 2216,1,11⟩,⟨.covers 3336,1,16⟩,⟨.covers 3592,1,6⟩,⟨.incident 3,8,-34⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source01.alphabets pointList := by
  rw [← fastListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source01.rootCodes link01 points rows bound = true := by decide +kernel

end C13.Global.FastDual01_003
namespace C13.Global.FastDual01_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,10,11]
def points : Finset C13.Point := {2,3,10,11}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,823,827,829,830,883,885,886,889,890,892,947,949,950,953,954,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1395,1402,1447,1459,1461,1497,1498,1509,1510,1521,1522,1524,1528,1639,1651,1654,1691,1715,1721,1753,1754,1765,1766,1777,1778,1780,1784,1819,1831,1843,1882,1894,1906,1945,1957,1969,2008,2020,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2419,2425,2455,2483,2486,2517,2518,2537,2538,2545,2546,2548,2552,2647,2675,2677,2731,2739,2746,2773,2774,2793,2794,2801,2802,2804,2808,2839,2859,2867,2901,2921,2929,2966,2986,2994,3028,3048,3056,3187,3251,3277,3278,3292,3308,3313,3314,3316,3320,3379,3532,3568,3635,3788,3824]
def rows : List LinearRow := [⟨.covers 75,1,7⟩,⟨.covers 139,1,4⟩,⟨.covers 269,1,33⟩,⟨.covers 1037,1,33⟩,⟨.covers 89,1,7⟩,⟨.covers 169,1,4⟩,⟨.covers 1289,1,9⟩,⟨.covers 2569,1,13⟩,⟨.covers 270,1,33⟩,⟨.covers 1038,1,33⟩,⟨.covers 154,1,4⟩,⟨.covers 106,1,7⟩,⟨.covers 2314,1,9⟩,⟨.covers 1546,1,13⟩,⟨.covers 108,1,22⟩,⟨.covers 1292,1,33⟩,⟨.covers 1548,1,33⟩,⟨.covers 344,1,6⟩,⟨.covers 1112,1,4⟩,⟨.covers 664,1,6⟩,⟨.covers 1176,1,7⟩,⟨.covers 360,1,6⟩,⟨.covers 2152,1,4⟩,⟨.covers 680,1,6⟩,⟨.covers 2216,1,7⟩,⟨.covers 1800,1,11⟩,⟨.covers 2824,1,11⟩,⟨.incident 3,8,-33⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source01.alphabets pointList := by
  rw [← fastListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source01.rootCodes link01 points rows bound = true := by decide +kernel

end C13.Global.FastDual01_004
namespace C13.Global.FastDual01_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,8]
def points : Finset C13.Point := {2,6,7,8}
def columns : List Code := [379,439,631,699,829,830,859,875,971,979,995,1371,1387,1402,1447,1453,1461,1595,1639,1646,1654,1691,1707,1721,1837,1852,1867,1882,1957,1987,2395,2411,2425,2455,2462,2486,2619,2647,2653,2677,2715,2731,2746,2846,2876,2891,2921,2966,3011,3131,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3611,3627,3635,3641,3642,3655,3661,3662,3669,3670,3676,3685,3686,3692,3700,3723,3737,3738,3753,3754,3768,3788]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 75,1,2⟩,⟨.covers 139,1,3⟩,⟨.covers 77,1,2⟩,⟨.covers 141,1,3⟩,⟨.covers 269,1,6⟩,⟨.covers 149,1,12⟩,⟨.covers 101,1,1⟩,⟨.covers 89,1,4⟩,⟨.covers 1049,1,2⟩,⟨.covers 169,1,3⟩,⟨.covers 201,1,9⟩,⟨.covers 2129,1,2⟩,⟨.covers 1553,1,2⟩,⟨.covers 2145,1,2⟩,⟨.covers 526,1,2⟩,⟨.covers 86,1,1⟩,⟨.covers 198,1,15⟩,⟨.covers 774,1,3⟩,⟨.covers 1286,1,12⟩,⟨.covers 154,1,3⟩,⟨.covers 106,1,4⟩,⟨.covers 2090,1,2⟩,⟨.covers 1106,1,2⟩,⟨.covers 1122,1,2⟩,⟨.covers 2594,1,2⟩,⟨.covers 156,1,9⟩,⟨.covers 116,1,1⟩,⟨.covers 212,1,6⟩,⟨.covers 228,1,15⟩,⟨.covers 3588,1,2⟩,⟨.covers 3336,1,6⟩,⟨.covers 464,1,11⟩,⟨.covers 2384,1,2⟩,⟨.covers 1616,1,2⟩,⟨.covers 912,1,6⟩,⟨.covers 2704,1,3⟩,⟨.covers 1808,1,6⟩,⟨.covers 480,1,8⟩,⟨.covers 1376,1,2⟩,⟨.covers 2656,1,2⟩,⟨.covers 928,1,9⟩,⟨.covers 2464,1,12⟩,⟨.covers 1696,1,3⟩,⟨.covers 2848,1,6⟩,⟨.covers 1472,1,17⟩,⟨.covers 2496,1,8⟩,⟨.covers 2752,1,9⟩,⟨.covers 3712,1,3⟩,⟨.incident 6,8,-5⟩,⟨.incident 7,8,-6⟩,⟨.incident 8,8,-2⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source01.alphabets pointList := by
  rw [← fastListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source01.rootCodes link01 points rows bound = true := by decide +kernel

end C13.Global.FastDual01_005
namespace C13.Global.FastDual01_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,10]
def points : Finset C13.Point := {2,6,7,10}
def columns : List Code := [379,439,631,699,823,827,829,830,859,875,883,923,939,947,971,979,995,1339,1371,1402,1447,1453,1461,1595,1639,1646,1654,1691,1721,1819,1831,1843,1882,1894,1906,1945,1957,1969,2363,2395,2411,2425,2455,2462,2486,2619,2647,2653,2677,2715,2731,2746,2839,2843,2845,2846,2859,2867,2869,2870,2873,2874,2876,2891,2899,2901,2905,2915,2921,2929,2955,2963,2966,2970,2979,2986,2994,3011,3131,3277,3278,3292,3308,3355,3379,3418,3469,3493,3532,3611,3635,3662,3686,3737,3788]
def rows : List LinearRow := [⟨.covers 2055,1,11⟩,⟨.covers 75,1,2⟩,⟨.covers 139,1,2⟩,⟨.covers 1035,1,8⟩,⟨.covers 2059,1,2⟩,⟨.covers 269,1,6⟩,⟨.covers 525,1,4⟩,⟨.covers 101,1,11⟩,⟨.covers 197,1,11⟩,⟨.covers 169,1,4⟩,⟨.covers 78,1,4⟩,⟨.covers 270,1,10⟩,⟨.covers 166,1,11⟩,⟨.covers 106,1,4⟩,⟨.covers 202,1,6⟩,⟨.covers 92,1,7⟩,⟨.covers 1548,1,2⟩,⟨.covers 228,1,11⟩,⟨.covers 1796,1,11⟩,⟨.covers 120,1,4⟩,⟨.covers 184,1,4⟩,⟨.covers 2344,1,2⟩,⟨.covers 2600,1,2⟩,⟨.covers 1800,1,2⟩,⟨.covers 1136,1,2⟩,⟨.covers 1200,1,2⟩,⟨.covers 464,1,11⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,8⟩,⟨.covers 3152,1,4⟩,⟨.covers 1424,1,8⟩,⟨.covers 2704,1,4⟩,⟨.covers 480,1,11⟩,⟨.covers 2848,1,1⟩,⟨.covers 3360,1,11⟩,⟨.covers 3616,1,11⟩,⟨.covers 1472,1,11⟩,⟨.covers 1728,1,2⟩,⟨.covers 2880,1,5⟩,⟨.covers 2944,1,5⟩,⟨.covers 3712,1,6⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source01.alphabets pointList := by
  rw [← fastListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source01.rootCodes link01 points rows bound = true := by decide +kernel

end C13.Global.FastDual01_006
namespace C13.Global.FastDual01_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,8,9]
def points : Finset C13.Point := {2,6,8,9}
def columns : List Code := [379,439,445,446,475,491,631,699,829,830,956,971,979,995,1211,1262,1371,1387,1402,1447,1453,1461,1462,1468,1483,1498,1639,1646,1654,1691,1707,1721,1722,1766,1852,1987,2235,2269,2395,2411,2425,2455,2462,2485,2486,2492,2507,2537,2647,2653,2677,2715,2731,2745,2746,2773,2876,3011,3131,3227,3243,3251,3257,3258,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,6⟩,⟨.covers 75,1,1⟩,⟨.covers 523,1,1⟩,⟨.covers 1043,1,1⟩,⟨.covers 2083,1,2⟩,⟨.covers 1037,1,7⟩,⟨.covers 149,1,3⟩,⟨.covers 773,1,2⟩,⟨.covers 2309,1,3⟩,⟨.covers 1541,1,7⟩,⟨.covers 89,1,3⟩,⟨.covers 1049,1,1⟩,⟨.covers 777,1,12⟩,⟨.covers 1289,1,5⟩,⟨.covers 2569,1,3⟩,⟨.covers 1073,1,2⟩,⟨.covers 1313,1,2⟩,⟨.covers 2337,1,2⟩,⟨.covers 526,1,1⟩,⟨.covers 2062,1,7⟩,⟨.covers 86,1,7⟩,⟨.covers 166,1,3⟩,⟨.covers 774,1,13⟩,⟨.covers 1286,1,3⟩,⟨.covers 106,1,3⟩,⟨.covers 2314,1,5⟩,⟨.covers 1546,1,3⟩,⟨.covers 2098,1,1⟩,⟨.covers 1298,1,2⟩,⟨.covers 2322,1,2⟩,⟨.covers 2210,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 1796,1,14⟩,⟨.covers 2820,1,14⟩,⟨.covers 3332,1,3⟩,⟨.covers 120,1,6⟩,⟨.covers 184,1,1⟩,⟨.covers 3336,1,3⟩,⟨.covers 1232,1,7⟩,⟨.covers 848,1,2⟩,⟨.covers 2384,1,3⟩,⟨.covers 912,1,12⟩,⟨.covers 1424,1,5⟩,⟨.covers 2704,1,3⟩,⟨.covers 736,1,1⟩,⟨.covers 2272,1,7⟩,⟨.covers 864,1,13⟩,⟨.covers 1376,1,3⟩,⟨.covers 2656,1,7⟩,⟨.covers 2464,1,5⟩,⟨.covers 1696,1,3⟩,⟨.covers 2752,1,1⟩,⟨.covers 1856,1,14⟩,⟨.covers 2880,1,13⟩,⟨.incident 8,8,-7⟩]
def bound : Int := 8

theorem column_mask : listMask columns = restrictMask universeMask Source01.alphabets pointList := by
  rw [← fastListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source01.rootCodes link01 points rows bound = true := by decide +kernel

end C13.Global.FastDual01_007
