import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source64
namespace C13.Global.FastDual64_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,2,3,5]
def points : Finset C13.Point := {0,2,3,5}
def columns : List Code := [253,764,830,892,956,979,1269,1447,1461,1498,1509,1654,1691,1747,1753,1754,1766,1780,1846,1852,1882,1894,1908,1939,1945,1946,1957,1958,1972,1987,2001,2002,2008,2020,2297,2411,2425,2518,2537,2647,2746,2771,2773,2774,2794,2808,2874,2876,2899,2901,2902,2921,2922,2936,2966,2986,3000,3011,3025,3026,3028,3048,3187,3251,3278,3286,3290,3292,3313,3379,3418,3427,3433,3441,3478,3491,3493,3505,3526,3530,3532,3538,3540,3544,3553,3635,3667,3669,3670,3686,3698,3731,3737,3738,3754,3762,3782,3786,3788,3793,3794,3796,3800,3810,3824,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 39,1,3⟩,⟨.covers 71,1,4⟩,⟨.covers 139,1,4⟩,⟨.covers 2059,1,3⟩,⟨.covers 525,1,1⟩,⟨.covers 3089,1,1⟩,⟨.covers 449,1,1⟩,⟨.covers 705,1,2⟩,⟨.covers 833,1,2⟩,⟨.covers 897,1,2⟩,⟨.covers 46,1,3⟩,⟨.covers 1038,1,4⟩,⟨.covers 1074,1,1⟩,⟨.covers 2098,1,1⟩,⟨.covers 610,1,1⟩,⟨.covers 1122,1,1⟩,⟨.covers 674,1,1⟩,⟨.covers 2210,1,1⟩,⟨.covers 404,1,1⟩,⟨.covers 2196,1,2⟩,⟨.covers 2324,1,2⟩,⟨.covers 1604,1,1⟩,⟨.covers 2436,1,2⟩,⟨.covers 344,1,1⟩,⟨.covers 1112,1,2⟩,⟨.covers 1304,1,2⟩,⟨.covers 1352,1,2⟩,⟨.covers 2696,1,1⟩,⟨.covers 624,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 688,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 1328,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 1248,1,1⟩,⟨.covers 2272,1,1⟩,⟨.covers 864,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 928,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 3616,1,2⟩,⟨.incident 0,8,3⟩,⟨.incident 2,8,3⟩,⟨.incident 3,8,3⟩,⟨.incident 5,8,1⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_000
namespace C13.Global.FastDual64_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,2,3,11]
def points : Finset C13.Point := {0,2,3,11}
def columns : List Code := [247,251,253,254,499,501,502,505,506,508,755,757,758,761,762,764,830,886,890,892,950,954,956,979,995,1009,1010,1012,1016,1267,1269,1270,1273,1274,1276,1402,1447,1459,1461,1462,1498,1507,1509,1510,1521,1522,1524,1528,1654,1691,1715,1721,1722,1747,1753,1754,1766,1777,1778,1780,1784,1846,1850,1852,1882,1894,1906,1908,1912,1939,1945,1946,1955,1957,1958,1969,1970,1972,1976,1987,2001,2002,2008,2017,2018,2020,2032,2291,2293,2294,2297,2298,2300,2411,2419,2425,2486,2518,2537,2538,2545,2546,2548,2552,2647,2675,2677,2746,2773,2774,2794,2801,2802,2804,2808,2901,2921,2929,2966,2986,2994,3028,3048,3056,3187,3251,3278,3286,3292,3306,3308,3313,3314,3316,3320,3379,3433,3441,3478,3506,3532,3540,3560,3568,3635,3669,3697,3754,3762,3788,3796,3816,3824,3853,3861,3881,3889,3980,3988,4008,4016]
def rows : List LinearRow := [⟨.covers 39,1,4⟩,⟨.covers 519,1,3⟩,⟨.covers 43,1,3⟩,⟨.covers 523,1,4⟩,⟨.covers 45,1,1⟩,⟨.covers 1073,1,1⟩,⟨.covers 449,1,2⟩,⟨.covers 705,1,2⟩,⟨.covers 833,1,1⟩,⟨.covers 897,1,2⟩,⟨.covers 526,1,4⟩,⟨.covers 1038,1,3⟩,⟨.covers 2322,1,1⟩,⟨.covers 3090,1,1⟩,⟨.covers 2594,1,1⟩,⟨.covers 3106,1,1⟩,⟨.covers 2434,1,1⟩,⟨.covers 2690,1,1⟩,⟨.covers 404,1,1⟩,⟨.covers 612,1,2⟩,⟨.covers 1124,1,2⟩,⟨.covers 1572,1,2⟩,⟨.covers 1604,1,1⟩,⟨.covers 344,1,2⟩,⟨.covers 1112,1,2⟩,⟨.covers 1304,1,2⟩,⟨.covers 680,1,1⟩,⟨.covers 1352,1,1⟩,⟨.covers 2224,1,2⟩,⟨.covers 2384,1,1⟩,⟨.covers 3152,1,1⟩,⟨.covers 2832,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 2848,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 3456,1,1⟩,⟨.covers 3712,1,1⟩,⟨.incident 0,8,3⟩,⟨.incident 2,8,3⟩,⟨.incident 3,8,3⟩,⟨.incident 11,8,1⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_001
namespace C13.Global.FastDual64_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,2,5,7]
def points : Finset C13.Point := {0,2,5,7}
def columns : List Code := [638,731,830,892,971,979,1447,1453,1461,1509,1646,1654,1691,1753,1838,1846,1852,1882,1894,1900,1908,1931,1939,1945,1957,1987,1993,2001,2171,2270,2411,2425,2462,2518,2647,2651,2653,2654,2682,2746,2778,2794,2846,2874,2876,2891,2899,2901,2902,2905,2906,2908,2921,2922,2936,2966,2970,2986,3011,3018,3026,3131,3187,3278,3292,3371,3379,3385,3418,3427,3433,3441,3470,3478,3484,3493,3526,3532,3540,3611,3635,3642,3662,3667,3669,3670,3673,3674,3676,3686,3690,3698,3737,3738,3754,3786,3788,3800,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 39,1,2⟩,⟨.covers 71,1,2⟩,⟨.covers 1035,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 45,1,2⟩,⟨.covers 77,1,2⟩,⟨.covers 53,1,2⟩,⟨.covers 101,1,2⟩,⟨.covers 773,1,1⟩,⟨.covers 57,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 1038,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 1298,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 184,1,2⟩,⟨.covers 232,1,2⟩,⟨.covers 1352,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 1232,1,1⟩,⟨.covers 3232,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_002
namespace C13.Global.FastDual64_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,2,5,9]
def points : Finset C13.Point := {0,2,5,9}
def columns : List Code := [253,638,731,764,830,892,956,971,979,985,1269,1447,1453,1461,1498,1509,1646,1654,1691,1747,1753,1766,1780,1838,1852,1894,1908,1931,1945,1987,2001,2171,2270,2297,2411,2425,2462,2518,2522,2524,2537,2647,2653,2746,2771,2773,2777,2794,2808,2876,2901,2986,3000,3011,3025,3131,3187,3251,3278,3286,3290,3292,3313,3371,3379,3385,3418,3427,3433,3441,3470,3478,3482,3484,3491,3493,3497,3505,3526,3530,3532,3538,3540,3544,3553,3669,3686,3737,3754,3793,3810,3824]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 71,1,2⟩,⟨.covers 525,1,1⟩,⟨.covers 1037,1,2⟩,⟨.covers 197,1,2⟩,⟨.covers 773,1,2⟩,⟨.covers 1541,1,2⟩,⟨.covers 54,1,2⟩,⟨.covers 166,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 1548,1,2⟩,⟨.covers 2572,1,1⟩,⟨.covers 404,1,1⟩,⟨.covers 864,1,2⟩,⟨.incident 2,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_003
namespace C13.Global.FastDual64_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,2,5,10]
def points : Finset C13.Point := {0,2,5,10}
def columns : List Code := [253,638,731,764,830,892,956,971,979,985,986,1269,1447,1453,1461,1498,1509,1646,1654,1691,1753,1754,1766,1780,1882,1894,1945,1957,2008,2020,2171,2270,2297,2411,2425,2462,2518,2522,2524,2537,2647,2651,2653,2654,2682,2746,2771,2773,2774,2777,2778,2780,2794,2808,2846,2874,2876,2891,2899,2901,2902,2905,2906,2908,2921,2922,2936,2966,2970,2972,2986,3000,3011,3017,3018,3025,3026,3028,3032,3048,3131,3187,3251,3278,3290,3292,3313,3379,3418,3493,3505,3532,3544,3611,3635,3662,3674,3686,3698,3737,3788,3800,3824]
def rows : List LinearRow := [⟨.covers 39,1,2⟩,⟨.covers 71,1,2⟩,⟨.covers 43,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 525,1,2⟩,⟨.covers 1037,1,2⟩,⟨.covers 101,1,1⟩,⟨.covers 1541,1,2⟩,⟨.covers 3077,1,2⟩,⟨.covers 777,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 1328,1,1⟩,⟨.covers 1376,1,1⟩,⟨.incident 0,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_004
namespace C13.Global.FastDual64_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,2,5,11]
def points : Finset C13.Point := {0,2,5,11}
def columns : List Code := [253,638,731,764,830,892,956,971,979,985,986,1269,1447,1453,1461,1498,1509,1646,1654,1691,1747,1753,1754,1766,1780,1838,1846,1852,1882,1894,1900,1908,1931,1939,1945,1946,1957,1958,1964,1972,1987,1993,1994,2001,2002,2008,2020,2171,2270,2297,2411,2425,2462,2518,2524,2537,2647,2653,2746,2773,2774,2780,2794,2808,2901,2921,2966,2986,3028,3048,3131,3187,3251,3278,3286,3292,3313,3371,3379,3433,3441,3470,3478,3532,3540,3635,3669,3754,3762,3788,3796,3824,3853,3861,3881,3889,3980,3988,4008,4016]
def rows : List LinearRow := [⟨.covers 39,1,33⟩,⟨.covers 71,1,29⟩,⟨.covers 75,1,12⟩,⟨.covers 139,1,5⟩,⟨.covers 1035,1,36⟩,⟨.covers 147,1,17⟩,⟨.covers 99,1,20⟩,⟨.covers 1539,1,17⟩,⟨.covers 45,1,24⟩,⟨.covers 77,1,1⟩,⟨.covers 53,1,6⟩,⟨.covers 1541,1,4⟩,⟨.covers 3077,1,2⟩,⟨.covers 537,1,12⟩,⟨.covers 2121,1,3⟩,⟨.covers 705,1,29⟩,⟨.covers 833,1,12⟩,⟨.covers 897,1,29⟩,⟨.covers 46,1,25⟩,⟨.covers 142,1,23⟩,⟨.covers 1038,1,10⟩,⟨.covers 54,1,15⟩,⟨.covers 774,1,6⟩,⟨.covers 3078,1,13⟩,⟨.covers 2322,1,13⟩,⟨.covers 1122,1,14⟩,⟨.covers 674,1,9⟩,⟨.covers 2210,1,19⟩,⟨.covers 1570,1,5⟩,⟨.covers 2594,1,14⟩,⟨.covers 2690,1,4⟩,⟨.covers 300,1,8⟩,⟨.covers 2572,1,13⟩,⟨.covers 180,1,1⟩,⟨.covers 308,1,5⟩,⟨.covers 404,1,20⟩,⟨.covers 1604,1,6⟩,⟨.covers 3140,1,3⟩,⟨.covers 3588,1,10⟩,⟨.covers 344,1,5⟩,⟨.covers 1112,1,45⟩,⟨.covers 1304,1,46⟩,⟨.covers 1352,1,17⟩,⟨.covers 3144,1,7⟩,⟨.covers 2696,1,9⟩,⟨.covers 624,1,20⟩,⟨.covers 688,1,7⟩,⟨.covers 2352,1,23⟩,⟨.covers 2384,1,5⟩,⟨.covers 2832,1,13⟩,⟨.covers 1248,1,25⟩,⟨.covers 2272,1,7⟩,⟨.covers 864,1,21⟩,⟨.covers 1376,1,7⟩,⟨.covers 3168,1,1⟩,⟨.covers 2464,1,7⟩,⟨.covers 2496,1,18⟩,⟨.covers 3456,1,10⟩,⟨.covers 3712,1,2⟩,⟨.incident 0,8,27⟩,⟨.incident 2,8,30⟩,⟨.incident 5,8,24⟩,⟨.incident 11,8,27⟩]
def bound : Int := 114

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_005
namespace C13.Global.FastDual64_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,2,7,9]
def points : Finset C13.Point := {0,2,7,9}
def columns : List Code := [638,731,830,886,892,971,979,995,1402,1447,1453,1461,1509,1646,1654,1660,1691,1721,1753,1838,1852,1894,1908,1931,1945,1987,2001,2171,2270,2411,2419,2425,2426,2462,2486,2518,2647,2653,2677,2678,2684,2746,2794,2876,2901,2932,2986,3011,3042,3131,3187,3193,3194,3278,3292,3308,3371,3379,3385,3386,3418,3427,3433,3434,3441,3442,3448,3470,3478,3484,3493,3494,3500,3508,3526,3532,3540,3556,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 39,1,18⟩,⟨.covers 71,1,18⟩,⟨.covers 147,1,13⟩,⟨.covers 99,1,5⟩,⟨.covers 2307,1,5⟩,⟨.covers 1539,1,1⟩,⟨.covers 45,1,18⟩,⟨.covers 77,1,13⟩,⟨.covers 53,1,4⟩,⟨.covers 149,1,5⟩,⟨.covers 101,1,10⟩,⟨.covers 773,1,18⟩,⟨.covers 3077,1,13⟩,⟨.covers 57,1,5⟩,⟨.covers 329,1,2⟩,⟨.covers 777,1,12⟩,⟨.covers 2569,1,5⟩,⟨.covers 3081,1,5⟩,⟨.covers 113,1,5⟩,⟨.covers 177,1,10⟩,⟨.covers 209,1,1⟩,⟨.covers 225,1,8⟩,⟨.covers 1793,1,1⟩,⟨.covers 3329,1,5⟩,⟨.covers 3585,1,5⟩,⟨.covers 54,1,4⟩,⟨.covers 1094,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 3078,1,4⟩,⟨.covers 1074,1,1⟩,⟨.covers 2194,1,1⟩,⟨.covers 3090,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 108,1,2⟩,⟨.covers 2316,1,2⟩,⟨.covers 1548,1,2⟩,⟨.covers 212,1,4⟩,⟨.covers 1796,1,2⟩,⟨.covers 792,1,1⟩,⟨.covers 232,1,2⟩,⟨.covers 360,1,1⟩,⟨.covers 1224,1,1⟩,⟨.covers 2376,1,1⟩,⟨.covers 2824,1,2⟩,⟨.covers 2224,1,1⟩,⟨.covers 864,1,1⟩,⟨.covers 3616,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 1728,1,12⟩,⟨.incident 0,8,-12⟩,⟨.incident 2,8,-4⟩]
def bound : Int := 3

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_006
namespace C13.Global.FastDual64_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,2,7,10]
def points : Finset C13.Point := {0,2,7,10}
def columns : List Code := [638,731,830,886,890,892,971,979,995,1402,1447,1453,1461,1509,1646,1654,1658,1691,1721,1753,1882,1894,1906,1945,1957,1969,2171,2270,2411,2419,2425,2426,2462,2486,2518,2647,2651,2653,2654,2675,2677,2678,2681,2682,2684,2746,2778,2794,2846,2870,2874,2876,2891,2899,2901,2902,2905,2906,2908,2915,2921,2922,2929,2930,2932,2936,2966,2970,2986,2994,3011,3018,3026,3042,3131,3187,3194,3278,3292,3308,3379,3418,3442,3493,3532,3556,3611,3635,3662,3674,3686,3698,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 39,1,7⟩,⟨.covers 71,1,11⟩,⟨.covers 43,1,1⟩,⟨.covers 1035,1,10⟩,⟨.covers 147,1,2⟩,⟨.covers 99,1,6⟩,⟨.covers 45,1,11⟩,⟨.covers 77,1,11⟩,⟨.covers 149,1,11⟩,⟨.covers 101,1,3⟩,⟨.covers 197,1,6⟩,⟨.covers 773,1,3⟩,⟨.covers 1541,1,2⟩,⟨.covers 3077,1,10⟩,⟨.covers 57,1,1⟩,⟨.covers 201,1,6⟩,⟨.covers 329,1,5⟩,⟨.covers 113,1,4⟩,⟨.covers 209,1,3⟩,⟨.covers 225,1,2⟩,⟨.covers 2817,1,3⟩,⟨.covers 3329,1,2⟩,⟨.covers 3585,1,2⟩,⟨.covers 46,1,6⟩,⟨.covers 1038,1,5⟩,⟨.covers 54,1,1⟩,⟨.covers 166,1,4⟩,⟨.covers 774,1,2⟩,⟨.covers 3078,1,6⟩,⟨.covers 2434,1,1⟩,⟨.covers 156,1,5⟩,⟨.covers 108,1,1⟩,⟨.covers 2316,1,6⟩,⟨.covers 116,1,4⟩,⟨.covers 212,1,6⟩,⟨.covers 1796,1,6⟩,⟨.covers 2820,1,3⟩,⟨.covers 184,1,6⟩,⟨.covers 312,1,2⟩,⟨.covers 232,1,10⟩,⟨.covers 808,1,1⟩,⟨.covers 1800,1,10⟩,⟨.covers 3336,1,2⟩,⟨.covers 1136,1,2⟩,⟨.covers 2224,1,6⟩,⟨.covers 1584,1,5⟩,⟨.covers 848,1,2⟩,⟨.covers 912,1,2⟩,⟨.covers 3344,1,10⟩,⟨.covers 736,1,1⟩,⟨.covers 864,1,2⟩,⟨.covers 1824,1,1⟩,⟨.covers 3616,1,5⟩,⟨.covers 2496,1,4⟩,⟨.covers 1728,1,2⟩,⟨.covers 2944,1,3⟩,⟨.covers 3712,1,10⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_007
