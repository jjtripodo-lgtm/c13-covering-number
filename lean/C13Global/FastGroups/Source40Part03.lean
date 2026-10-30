import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source40
namespace C13.Global.FastDual40_024
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,9,11]
def points : Finset C13.Point := {1,7,9,11}
def columns : List Code := [381,471,637,747,829,861,885,892,967,971,979,995,1143,1147,1149,1150,1213,1245,1261,1341,1367,1371,1373,1374,1389,1395,1397,1398,1401,1402,1404,1437,1453,1461,1485,1493,1509,1597,1629,1639,1646,1653,1654,1660,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2173,2238,2397,2413,2421,2425,2455,2462,2486,2518,2653,2677,2731,2734,2746,2794,2901,2986,3127,3131,3165,3181,3187,3189,3193,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 519,1,5⟩,⟨.covers 2055,1,4⟩,⟨.covers 267,1,10⟩,⟨.covers 1035,1,1⟩,⟨.covers 2059,1,7⟩,⟨.covers 147,1,7⟩,⟨.covers 99,1,3⟩,⟨.covers 1059,1,1⟩,⟨.covers 2563,1,4⟩,⟨.covers 141,1,4⟩,⟨.covers 525,1,6⟩,⟨.covers 2061,1,5⟩,⟨.covers 297,1,2⟩,⟨.covers 777,1,1⟩,⟨.covers 3081,1,2⟩,⟨.covers 78,1,4⟩,⟨.covers 270,1,7⟩,⟨.covers 1062,1,1⟩,⟨.covers 774,1,5⟩,⟨.covers 2566,1,11⟩,⟨.covers 3078,1,4⟩,⟨.covers 1546,1,4⟩,⟨.covers 114,1,3⟩,⟨.covers 210,1,4⟩,⟨.covers 2818,1,11⟩,⟨.covers 3330,1,2⟩,⟨.covers 2316,1,4⟩,⟨.covers 1548,1,1⟩,⟨.covers 180,1,7⟩,⟨.covers 228,1,7⟩,⟨.covers 2820,1,11⟩,⟨.covers 3588,1,11⟩,⟨.covers 120,1,2⟩,⟨.covers 312,1,2⟩,⟨.covers 216,1,7⟩,⟨.covers 1800,1,3⟩,⟨.covers 624,1,3⟩,⟨.covers 2160,1,3⟩,⟨.covers 432,1,4⟩,⟨.covers 1584,1,4⟩,⟨.covers 2704,1,11⟩,⟨.covers 3216,1,4⟩,⟨.covers 480,1,4⟩,⟨.covers 2272,1,4⟩,⟨.covers 864,1,4⟩,⟨.covers 2656,1,5⟩,⟨.covers 1696,1,7⟩,⟨.covers 1824,1,1⟩,⟨.covers 3360,1,7⟩,⟨.covers 2496,1,7⟩,⟨.covers 1728,1,4⟩,⟨.covers 2752,1,2⟩,⟨.covers 1920,1,7⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_024
namespace C13.Global.FastDual40_025
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,7]
def points : Finset C13.Point := {2,3,6,7}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,979,995,1371,1402,1447,1461,1639,1654,1691,1721,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1955,1957,1969,1987,2411,2425,2455,2486,2647,2677,2731,2746,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2966,2979,2986,2994,3011,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3477,3478,3493,3494,3508,3532,3635,3655,3669,3670,3685,3686,3700,3723,3737,3738,3753,3754,3768,3788,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 135,1,6⟩,⟨.covers 75,1,6⟩,⟨.covers 139,1,6⟩,⟨.covers 77,1,33⟩,⟨.covers 149,1,6⟩,⟨.covers 101,1,6⟩,⟨.covers 89,1,6⟩,⟨.covers 169,1,6⟩,⟨.covers 2369,1,6⟩,⟨.covers 2625,1,6⟩,⟨.covers 78,1,33⟩,⟨.covers 86,1,6⟩,⟨.covers 166,1,6⟩,⟨.covers 154,1,6⟩,⟨.covers 106,1,6⟩,⟨.covers 210,1,33⟩,⟨.covers 226,1,33⟩,⟨.covers 2434,1,6⟩,⟨.covers 2690,1,6⟩,⟨.covers 92,1,33⟩,⟨.covers 108,1,33⟩,⟨.covers 1604,1,6⟩,⟨.covers 1412,1,6⟩,⟨.covers 1352,1,6⟩,⟨.covers 1672,1,6⟩,⟨.covers 2160,1,6⟩,⟨.covers 2224,1,6⟩,⟨.covers 1616,1,6⟩,⟨.covers 1424,1,6⟩,⟨.covers 1376,1,6⟩,⟨.covers 1696,1,6⟩,⟨.covers 2496,1,11⟩,⟨.covers 1728,1,11⟩,⟨.incident 6,8,-17⟩,⟨.incident 7,8,-17⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_025
namespace C13.Global.FastDual40_026
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,8]
def points : Finset C13.Point := {2,3,6,8}
def columns : List Code := [254,379,439,506,631,699,758,829,830,949,950,956,979,995,1010,1371,1402,1447,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1852,1882,1957,1972,1987,2002,2300,2411,2425,2455,2485,2486,2537,2552,2647,2677,2731,2739,2745,2746,2773,2804,2876,2921,2966,2996,3011,3041,3056,3251,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3635,3655,3669,3670,3685,3686,3700,3723,3731,3737,3738,3747,3753,3754,3761,3762,3768,3781,3782,3788,3796,3812,3854,3884,3914,3944,3974,4004,4034,4064]
def rows : List LinearRow := [⟨.covers 71,1,22⟩,⟨.covers 135,1,10⟩,⟨.covers 1031,1,17⟩,⟨.covers 2055,1,11⟩,⟨.covers 75,1,17⟩,⟨.covers 139,1,19⟩,⟨.covers 2059,1,18⟩,⟨.covers 77,1,24⟩,⟨.covers 269,1,36⟩,⟨.covers 101,1,12⟩,⟨.covers 2309,1,19⟩,⟨.covers 89,1,13⟩,⟨.covers 169,1,19⟩,⟨.covers 2569,1,19⟩,⟨.covers 2129,1,19⟩,⟨.covers 1313,1,20⟩,⟨.covers 449,1,17⟩,⟨.covers 705,1,12⟩,⟨.covers 833,1,15⟩,⟨.covers 2625,1,1⟩,⟨.covers 897,1,7⟩,⟨.covers 78,1,20⟩,⟨.covers 270,1,18⟩,⟨.covers 1038,1,1⟩,⟨.covers 278,1,8⟩,⟨.covers 1094,1,3⟩,⟨.covers 282,1,5⟩,⟨.covers 554,1,5⟩,⟨.covers 1074,1,2⟩,⟨.covers 2098,1,40⟩,⟨.covers 2322,1,6⟩,⟨.covers 3090,1,17⟩,⟨.covers 3106,1,51⟩,⟨.covers 706,1,6⟩,⟨.covers 2818,1,2⟩,⟨.covers 2316,1,15⟩,⟨.covers 2324,1,12⟩,⟨.covers 2580,1,1⟩,⟨.covers 228,1,4⟩,⟨.covers 1188,1,18⟩,⟨.covers 664,1,36⟩,⟨.covers 1560,1,2⟩,⟨.covers 1672,1,24⟩,⟨.covers 624,1,20⟩,⟨.covers 1328,1,13⟩,⟨.covers 464,1,8⟩,⟨.covers 2256,1,20⟩,⟨.covers 2384,1,3⟩,⟨.covers 1616,1,29⟩,⟨.covers 3152,1,4⟩,⟨.covers 1424,1,14⟩,⟨.covers 736,1,8⟩,⟨.covers 1376,1,15⟩,⟨.covers 1824,1,20⟩,⟨.covers 1472,1,8⟩,⟨.covers 2944,1,5⟩,⟨.covers 3456,1,8⟩,⟨.incident 2,8,28⟩,⟨.incident 3,8,30⟩,⟨.incident 6,8,28⟩,⟨.incident 8,8,17⟩]
def bound : Int := 111

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_026
namespace C13.Global.FastDual40_027
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,9]
def points : Finset C13.Point := {2,3,6,9}
def columns : List Code := [254,379,439,506,631,699,758,829,830,953,954,956,979,995,1010,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1721,1722,1766,1852,1894,1945,1976,1987,2018,2300,2411,2425,2455,2483,2485,2486,2537,2552,2647,2677,2731,2745,2746,2773,2804,2876,2901,2986,3000,3011,3025,3056,3251,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3475,3477,3478,3491,3493,3494,3505,3506,3508,3529,3530,3532,3544,3560,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,8⟩,⟨.covers 77,1,25⟩,⟨.covers 149,1,8⟩,⟨.covers 101,1,25⟩,⟨.covers 773,1,25⟩,⟨.covers 270,1,8⟩,⟨.covers 1038,1,25⟩,⟨.covers 774,1,17⟩,⟨.covers 1286,1,8⟩,⟨.covers 2566,1,25⟩,⟨.covers 108,1,17⟩,⟨.covers 1292,1,17⟩,⟨.covers 1548,1,8⟩,⟨.covers 2572,1,25⟩,⟨.covers 212,1,8⟩,⟨.covers 404,1,8⟩,⟨.covers 1188,1,8⟩,⟨.covers 3332,1,8⟩,⟨.covers 1616,1,25⟩,⟨.incident 2,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_027
namespace C13.Global.FastDual40_028
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,11]
def points : Finset C13.Point := {2,3,6,11}
def columns : List Code := [254,379,439,506,631,699,758,823,827,829,830,883,947,949,950,953,954,956,979,995,1010,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1946,1955,1957,1958,1969,1970,1972,1976,1987,2002,2018,2300,2411,2425,2455,2483,2486,2537,2552,2647,2677,2731,2739,2746,2773,2804,2839,2859,2867,2901,2921,2929,2966,2986,2994,3056,3251,3277,3278,3292,3308,3379,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 135,1,4⟩,⟨.covers 1031,1,4⟩,⟨.covers 75,1,11⟩,⟨.covers 139,1,5⟩,⟨.covers 1035,1,2⟩,⟨.covers 77,1,14⟩,⟨.covers 269,1,17⟩,⟨.covers 149,1,10⟩,⟨.covers 101,1,7⟩,⟨.covers 197,1,3⟩,⟨.covers 89,1,1⟩,⟨.covers 169,1,9⟩,⟨.covers 449,1,4⟩,⟨.covers 1665,1,3⟩,⟨.covers 270,1,17⟩,⟨.covers 1038,1,17⟩,⟨.covers 86,1,1⟩,⟨.covers 1286,1,3⟩,⟨.covers 2566,1,12⟩,⟨.covers 106,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,3⟩,⟨.covers 210,1,4⟩,⟨.covers 226,1,4⟩,⟨.covers 1122,1,3⟩,⟨.covers 450,1,4⟩,⟨.covers 3330,1,11⟩,⟨.covers 3586,1,11⟩,⟨.covers 156,1,2⟩,⟨.covers 2316,1,17⟩,⟨.covers 2572,1,17⟩,⟨.covers 116,1,6⟩,⟨.covers 2132,1,1⟩,⟨.covers 1188,1,4⟩,⟨.covers 1796,1,7⟩,⟨.covers 2820,1,2⟩,⟨.covers 1176,1,2⟩,⟨.covers 360,1,1⟩,⟨.covers 1800,1,9⟩,⟨.covers 2824,1,13⟩,⟨.covers 2384,1,11⟩,⟨.covers 1616,1,1⟩,⟨.covers 3152,1,12⟩,⟨.covers 3168,1,13⟩,⟨.covers 1856,1,1⟩,⟨.incident 2,8,-3⟩,⟨.incident 3,8,-3⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_028
namespace C13.Global.FastDual40_029
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,8]
def points : Finset C13.Point := {2,3,7,8}
def columns : List Code := [379,439,631,699,829,830,889,890,892,979,995,1371,1401,1402,1447,1461,1509,1639,1651,1653,1654,1691,1721,1753,1852,1882,1912,1957,1987,2017,2411,2425,2426,2455,2486,2518,2647,2675,2677,2678,2731,2746,2794,2876,2921,2936,2966,3011,3026,3187,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3635,3655,3667,3669,3670,3683,3685,3686,3697,3698,3700,3723,3737,3738,3753,3754,3768,3785,3786,3788,3800,3816,3854,3884,3914,3944,3974,4004,4034,4064]
def rows : List LinearRow := [⟨.covers 139,1,8⟩,⟨.covers 77,1,28⟩,⟨.covers 2309,1,28⟩,⟨.covers 169,1,8⟩,⟨.covers 897,1,3⟩,⟨.covers 78,1,28⟩,⟨.covers 166,1,28⟩,⟨.covers 154,1,6⟩,⟨.covers 210,1,6⟩,⟨.covers 226,1,25⟩,⟨.covers 212,1,22⟩,⟨.covers 228,1,28⟩,⟨.covers 184,1,6⟩,⟨.covers 216,1,6⟩,⟨.covers 1672,1,14⟩,⟨.covers 2696,1,3⟩,⟨.covers 912,1,19⟩,⟨.covers 1424,1,28⟩,⟨.covers 2704,1,3⟩,⟨.covers 1920,1,25⟩,⟨.covers 3712,1,3⟩,⟨.incident 7,8,-28⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_029
namespace C13.Global.FastDual40_030
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,9]
def points : Finset C13.Point := {2,3,7,9}
def columns : List Code := [379,439,631,699,829,830,885,886,892,979,995,1371,1395,1401,1402,1447,1461,1509,1639,1653,1654,1691,1721,1753,1852,1894,1908,1945,1987,2001,2411,2419,2425,2426,2455,2486,2518,2647,2677,2678,2731,2746,2794,2876,2901,2932,2986,3011,3042,3187,3277,3278,3292,3308,3379,3403,3411,3417,3418,3427,3433,3434,3441,3442,3448,3463,3477,3478,3493,3494,3508,3525,3526,3532,3540,3556,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 77,1,2⟩,⟨.covers 269,1,2⟩,⟨.covers 101,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 78,1,2⟩,⟨.covers 270,1,2⟩,⟨.covers 1546,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 2704,1,1⟩,⟨.incident 2,8,-1⟩,⟨.incident 3,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_030
namespace C13.Global.FastDual40_031
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,11]
def points : Finset C13.Point := {2,3,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,883,885,886,889,890,892,947,979,995,1371,1395,1401,1402,1447,1461,1509,1639,1651,1653,1654,1691,1721,1753,1819,1831,1843,1845,1846,1849,1850,1852,1875,1881,1882,1891,1893,1894,1905,1906,1908,1912,1939,1945,1955,1957,1969,1987,2001,2017,2411,2419,2425,2455,2486,2518,2647,2675,2677,2731,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3187,3277,3278,3292,3308,3379,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 1035,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 2224,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 2880,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_031
