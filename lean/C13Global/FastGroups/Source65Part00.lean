import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source65
namespace C13.Global.FastDual65_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,5,6]
def points : Finset C13.Point := {0,3,5,6}
def columns : List Code := [702,727,830,956,967,979,1207,1246,1374,1447,1461,1498,1654,1687,1691,1693,1694,1718,1750,1766,1822,1846,1852,1878,1882,1894,1927,1939,1941,1942,1945,1946,1948,1957,1958,1972,1987,1990,2002,2411,2413,2425,2537,2647,2734,2746,2773,2862,2874,2876,2887,2899,2901,2921,2966,2986,2988,3000,3011,3013,3025,3127,3251,3278,3292,3367,3379,3381,3406,3418,3420,3433,3478,3491,3493,3505,3530,3532,3544,3607,3635,3638,3669,3670,3686,3726,3731,3733,3734,3737,3738,3740,3750,3754,3762,3782,3788,3796,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 39,1,5⟩,⟨.covers 71,1,1⟩,⟨.covers 2055,1,8⟩,⟨.covers 43,1,20⟩,⟨.covers 139,1,19⟩,⟨.covers 83,1,9⟩,⟨.covers 163,1,4⟩,⟨.covers 1283,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 45,1,20⟩,⟨.covers 141,1,19⟩,⟨.covers 53,1,6⟩,⟨.covers 197,1,7⟩,⟨.covers 773,1,5⟩,⟨.covers 3077,1,1⟩,⟨.covers 57,1,20⟩,⟨.covers 169,1,20⟩,⟨.covers 1289,1,9⟩,⟨.covers 3081,1,2⟩,⟨.covers 177,1,4⟩,⟨.covers 209,1,2⟩,⟨.covers 833,1,3⟩,⟨.covers 897,1,2⟩,⟨.covers 1409,1,4⟩,⟨.covers 46,1,2⟩,⟨.covers 78,1,2⟩,⟨.covers 1038,1,1⟩,⟨.covers 2062,1,8⟩,⟨.covers 58,1,8⟩,⟨.covers 202,1,5⟩,⟨.covers 778,1,3⟩,⟨.covers 2322,1,3⟩,⟨.covers 834,1,1⟩,⟨.covers 1346,1,4⟩,⟨.covers 2434,1,8⟩,⟨.covers 3586,1,3⟩,⟨.covers 92,1,4⟩,⟨.covers 172,1,9⟩,⟨.covers 1292,1,2⟩,⟨.covers 116,1,19⟩,⟨.covers 2324,1,8⟩,⟨.covers 228,1,19⟩,⟨.covers 804,1,2⟩,⟨.covers 1316,1,5⟩,⟨.covers 184,1,1⟩,⟨.covers 216,1,4⟩,⟨.covers 1304,1,4⟩,⟨.covers 808,1,5⟩,⟨.covers 2696,1,1⟩,⟨.covers 3208,1,1⟩,⟨.covers 2224,1,9⟩,⟨.covers 2608,1,1⟩,⟨.covers 1232,1,1⟩,⟨.covers 2256,1,8⟩,⟨.covers 848,1,3⟩,⟨.covers 3600,1,4⟩,⟨.covers 2656,1,11⟩,⟨.covers 928,1,3⟩,⟨.covers 3232,1,3⟩,⟨.covers 2752,1,2⟩,⟨.incident 0,8,-1⟩,⟨.incident 5,8,-2⟩]
def bound : Int := 19

theorem column_mask : listMask columns = restrictMask universeMask Source65.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source65.rootCodes link65 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual65_000
namespace C13.Global.FastDual65_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,5,9]
def points : Finset C13.Point := {0,3,5,9}
def columns : List Code := [253,702,727,764,830,892,956,967,979,981,1207,1246,1269,1374,1447,1461,1494,1498,1500,1509,1654,1691,1693,1747,1749,1753,1766,1780,1852,1894,1908,1945,1987,2001,2297,2411,2413,2425,2518,2537,2647,2734,2746,2771,2773,2794,2808,2862,2876,2887,2901,2986,3000,3011,3025,3127,3187,3251,3278,3286,3290,3292,3313,3367,3379,3381,3406,3414,3418,3420,3427,3429,3433,3441,3478,3491,3493,3505,3526,3530,3532,3538,3540,3544,3553,3669,3686,3737,3754,3793,3810,3824,3851,3865,3882,3896,3907,3921,3938,3952]
def rows : List LinearRow := [⟨.covers 43,1,17⟩,⟨.covers 139,1,33⟩,⟨.covers 525,1,33⟩,⟨.covers 2061,1,33⟩,⟨.covers 169,1,17⟩,⟨.covers 1289,1,17⟩,⟨.covers 58,1,33⟩,⟨.covers 106,1,17⟩,⟨.covers 202,1,17⟩,⟨.covers 1292,1,17⟩,⟨.covers 2572,1,33⟩,⟨.covers 120,1,17⟩,⟨.covers 344,1,17⟩,⟨.covers 3208,1,17⟩,⟨.covers 1800,1,17⟩,⟨.covers 928,1,33⟩,⟨.incident 3,8,-33⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source65.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source65.rootCodes link65 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual65_001
namespace C13.Global.FastDual65_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,5,10]
def points : Finset C13.Point := {0,3,5,10}
def columns : List Code := [253,702,727,764,830,892,956,967,979,981,982,1207,1246,1269,1374,1447,1461,1498,1500,1509,1654,1691,1693,1753,1754,1756,1766,1780,1882,1894,1945,1957,2008,2020,2297,2411,2413,2425,2518,2537,2647,2734,2746,2771,2773,2774,2794,2808,2862,2874,2876,2887,2899,2901,2902,2921,2922,2924,2936,2966,2986,2988,3000,3011,3013,3014,3025,3026,3028,3048,3127,3187,3251,3278,3290,3292,3313,3367,3379,3406,3418,3493,3505,3532,3544,3635,3686,3698,3737,3788,3800,3824]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 43,1,12⟩,⟨.covers 139,1,25⟩,⟨.covers 83,1,12⟩,⟨.covers 99,1,12⟩,⟨.covers 163,1,25⟩,⟨.covers 2563,1,6⟩,⟨.covers 525,1,6⟩,⟨.covers 2061,1,25⟩,⟨.covers 773,1,6⟩,⟨.covers 1541,1,19⟩,⟨.covers 3077,1,25⟩,⟨.covers 57,1,25⟩,⟨.covers 777,1,12⟩,⟨.covers 1289,1,12⟩,⟨.covers 2569,1,6⟩,⟨.covers 449,1,6⟩,⟨.covers 705,1,6⟩,⟨.covers 2817,1,6⟩,⟨.covers 3585,1,19⟩,⟨.covers 1328,1,25⟩,⟨.incident 0,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source65.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source65.rootCodes link65 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual65_002
namespace C13.Global.FastDual65_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,5,11]
def points : Finset C13.Point := {0,3,5,11}
def columns : List Code := [253,702,727,764,830,892,956,967,979,981,982,1207,1246,1269,1374,1447,1461,1494,1498,1500,1509,1654,1687,1691,1693,1694,1718,1747,1749,1750,1753,1754,1756,1766,1780,1822,1846,1852,1878,1882,1884,1894,1908,1927,1939,1941,1942,1945,1946,1948,1957,1958,1972,1987,1989,1990,2001,2002,2004,2008,2020,2297,2411,2413,2425,2518,2537,2647,2734,2746,2773,2774,2794,2808,2901,2921,2966,2986,3028,3048,3127,3187,3251,3278,3286,3292,3313,3379,3433,3441,3478,3532,3540,3607,3635,3669,3726,3734,3754,3762,3788,3796,3824]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 43,1,2⟩,⟨.covers 139,1,2⟩,⟨.covers 83,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 525,1,2⟩,⟨.covers 2061,1,2⟩,⟨.covers 3077,1,1⟩,⟨.covers 57,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 1793,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 2464,1,1⟩,⟨.incident 0,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source65.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source65.rootCodes link65 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual65_003
namespace C13.Global.FastDual65_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,6,9]
def points : Finset C13.Point := {0,3,6,9}
def columns : List Code := [702,727,830,954,956,967,979,995,1207,1246,1374,1402,1447,1459,1461,1462,1498,1654,1691,1693,1721,1722,1724,1766,1852,1894,1945,1976,1987,2018,2411,2413,2425,2486,2537,2647,2677,2734,2746,2748,2773,2862,2876,2887,2901,2986,3000,3011,3025,3127,3251,3253,3254,3278,3292,3308,3367,3379,3381,3382,3406,3418,3420,3433,3434,3436,3448,3478,3491,3493,3494,3505,3506,3508,3530,3532,3544,3560,3669,3686,3700,3737,3754,3768,3851,3865,3882,3896,3907,3921,3938,3952]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 139,1,2⟩,⟨.covers 83,1,2⟩,⟨.covers 99,1,2⟩,⟨.covers 141,1,2⟩,⟨.covers 101,1,2⟩,⟨.covers 773,1,2⟩,⟨.covers 3077,1,1⟩,⟨.covers 57,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 201,1,2⟩,⟨.covers 177,1,1⟩,⟨.covers 1409,1,1⟩,⟨.covers 1793,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 2752,1,2⟩,⟨.incident 0,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source65.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source65.rootCodes link65 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual65_004
namespace C13.Global.FastDual65_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,6,10]
def points : Finset C13.Point := {0,3,6,10}
def columns : List Code := [702,727,830,950,954,956,967,979,995,1207,1246,1374,1402,1447,1459,1461,1498,1654,1691,1693,1715,1717,1721,1766,1882,1894,1906,1945,1957,1969,2411,2413,2425,2486,2537,2647,2677,2734,2742,2746,2748,2773,2862,2870,2874,2876,2887,2899,2901,2915,2917,2921,2929,2966,2982,2986,2988,2994,2996,3000,3011,3013,3025,3041,3127,3251,3253,3278,3292,3308,3367,3379,3406,3418,3493,3505,3532,3544,3635,3686,3737,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 43,1,16⟩,⟨.covers 139,1,8⟩,⟨.covers 83,1,2⟩,⟨.covers 2067,1,2⟩,⟨.covers 163,1,5⟩,⟨.covers 387,1,1⟩,⟨.covers 1283,1,1⟩,⟨.covers 2563,1,2⟩,⟨.covers 45,1,16⟩,⟨.covers 141,1,12⟩,⟨.covers 53,1,2⟩,⟨.covers 2069,1,2⟩,⟨.covers 197,1,1⟩,⟨.covers 389,1,1⟩,⟨.covers 773,1,5⟩,⟨.covers 3077,1,2⟩,⟨.covers 57,1,11⟩,⟨.covers 201,1,6⟩,⟨.covers 1289,1,15⟩,⟨.covers 2569,1,11⟩,⟨.covers 3081,1,5⟩,⟨.covers 177,1,1⟩,⟨.covers 209,1,5⟩,⟨.covers 225,1,2⟩,⟨.covers 1793,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 3329,1,5⟩,⟨.covers 58,1,4⟩,⟨.covers 778,1,4⟩,⟨.covers 1546,1,8⟩,⟨.covers 3082,1,12⟩,⟨.covers 2690,1,4⟩,⟨.covers 3586,1,4⟩,⟨.covers 92,1,12⟩,⟨.covers 172,1,4⟩,⟨.covers 1548,1,4⟩,⟨.covers 2572,1,4⟩,⟨.covers 116,1,4⟩,⟨.covers 308,1,4⟩,⟨.covers 120,1,5⟩,⟨.covers 184,1,4⟩,⟨.covers 232,1,8⟩,⟨.covers 2824,1,4⟩,⟨.covers 1376,1,3⟩,⟨.covers 1824,1,1⟩,⟨.covers 1472,1,12⟩,⟨.covers 1728,1,4⟩,⟨.incident 0,8,-4⟩,⟨.incident 3,8,-8⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source65.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source65.rootCodes link65 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual65_005
namespace C13.Global.FastDual65_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,6,11]
def points : Finset C13.Point := {0,3,6,11}
def columns : List Code := [702,727,830,950,954,956,967,979,995,1207,1246,1374,1402,1447,1459,1461,1462,1498,1654,1687,1691,1693,1694,1715,1717,1718,1721,1722,1724,1750,1766,1822,1846,1850,1852,1878,1882,1894,1906,1927,1939,1941,1942,1945,1946,1948,1955,1957,1958,1969,1970,1972,1976,1987,1990,2002,2018,2411,2413,2425,2486,2537,2647,2677,2734,2742,2746,2773,2901,2921,2929,2966,2986,2994,3127,3251,3254,3278,3292,3308,3379,3433,3478,3506,3532,3560,3607,3635,3669,3726,3734,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 2055,1,4⟩,⟨.covers 43,1,11⟩,⟨.covers 139,1,11⟩,⟨.covers 83,1,6⟩,⟨.covers 163,1,4⟩,⟨.covers 1283,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 45,1,11⟩,⟨.covers 141,1,11⟩,⟨.covers 197,1,5⟩,⟨.covers 773,1,5⟩,⟨.covers 3077,1,6⟩,⟨.covers 89,1,5⟩,⟨.covers 169,1,2⟩,⟨.covers 201,1,2⟩,⟨.covers 777,1,4⟩,⟨.covers 2569,1,7⟩,⟨.covers 3081,1,11⟩,⟨.covers 113,1,6⟩,⟨.covers 177,1,5⟩,⟨.covers 225,1,5⟩,⟨.covers 1793,1,3⟩,⟨.covers 46,1,1⟩,⟨.covers 2062,1,4⟩,⟨.covers 774,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 58,1,5⟩,⟨.covers 202,1,5⟩,⟨.covers 778,1,2⟩,⟨.covers 3082,1,1⟩,⟨.covers 2818,1,9⟩,⟨.covers 3330,1,9⟩,⟨.covers 92,1,6⟩,⟨.covers 172,1,1⟩,⟨.covers 1292,1,4⟩,⟨.covers 2572,1,5⟩,⟨.covers 116,1,5⟩,⟨.covers 308,1,3⟩,⟨.covers 2324,1,1⟩,⟨.covers 228,1,6⟩,⟨.covers 420,1,3⟩,⟨.covers 184,1,4⟩,⟨.covers 1800,1,4⟩,⟨.covers 1136,1,6⟩,⟨.covers 2224,1,1⟩,⟨.covers 848,1,5⟩,⟨.covers 3152,1,5⟩,⟨.covers 736,1,1⟩,⟨.covers 1248,1,4⟩,⟨.covers 3616,1,9⟩,⟨.covers 1472,1,6⟩,⟨.covers 2496,1,1⟩,⟨.covers 2752,1,6⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source65.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source65.rootCodes link65 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual65_006
namespace C13.Global.FastDual65_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,9,10]
def points : Finset C13.Point := {0,3,9,10}
def columns : List Code := [247,251,253,254,382,487,499,501,502,505,506,508,702,727,755,757,758,761,762,764,830,886,892,954,956,967,979,981,995,998,1009,1010,1012,1016,1207,1246,1267,1269,1270,1273,1274,1276,1374,1398,1402,1447,1459,1461,1498,1500,1509,1510,1521,1522,1524,1528,1654,1691,1693,1721,1753,1766,1777,1778,1780,1784,1894,1945,2032,2167,2286,2291,2293,2294,2297,2298,2300,2407,2411,2413,2414,2419,2421,2422,2425,2426,2428,2486,2518,2531,2533,2534,2537,2538,2540,2545,2546,2548,2552,2647,2677,2678,2734,2746,2748,2771,2773,2790,2794,2801,2802,2804,2808,2862,2876,2887,2901,2918,2932,2986,3000,3011,3025,3042,3056,3127,3187,3190,3251,3253,3278,3290,3292,3302,3308,3313,3314,3316,3320,3367,3379,3406,3418,3430,3442,3493,3505,3532,3544,3556,3568,3686,3737,3824]
def rows : List LinearRow := [⟨.covers 135,1,7⟩,⟨.covers 519,1,5⟩,⟨.covers 1031,1,2⟩,⟨.covers 523,1,19⟩,⟨.covers 2059,1,19⟩,⟨.covers 83,1,1⟩,⟨.covers 163,1,6⟩,⟨.covers 1283,1,1⟩,⟨.covers 2563,1,7⟩,⟨.covers 525,1,19⟩,⟨.covers 2061,1,19⟩,⟨.covers 2069,1,1⟩,⟨.covers 773,1,1⟩,⟨.covers 3077,1,13⟩,⟨.covers 89,1,11⟩,⟨.covers 777,1,19⟩,⟨.covers 2569,1,19⟩,⟨.covers 1073,1,1⟩,⟨.covers 593,1,2⟩,⟨.covers 417,1,1⟩,⟨.covers 1185,1,2⟩,⟨.covers 449,1,5⟩,⟨.covers 2817,1,6⟩,⟨.covers 3329,1,2⟩,⟨.covers 142,1,8⟩,⟨.covers 526,1,4⟩,⟨.covers 1038,1,5⟩,⟨.covers 58,1,2⟩,⟨.covers 778,1,10⟩,⟨.covers 3082,1,2⟩,⟨.covers 1074,1,2⟩,⟨.covers 1106,1,5⟩,⟨.covers 2194,1,9⟩,⟨.covers 674,1,2⟩,⟨.covers 2434,1,1⟩,⟨.covers 1794,1,19⟩,⟨.covers 3586,1,19⟩,⟨.covers 92,1,1⟩,⟨.covers 172,1,2⟩,⟨.covers 1292,1,8⟩,⟨.covers 2572,1,2⟩,⟨.covers 116,1,5⟩,⟨.covers 564,1,1⟩,⟨.covers 596,1,3⟩,⟨.covers 404,1,8⟩,⟨.covers 2196,1,2⟩,⟨.covers 312,1,2⟩,⟨.covers 2248,1,4⟩,⟨.covers 2824,1,3⟩,⟨.covers 3336,1,5⟩,⟨.covers 1328,1,5⟩,⟨.covers 2608,1,5⟩,⟨.covers 1616,1,4⟩,⟨.covers 2832,1,6⟩,⟨.covers 3344,1,8⟩,⟨.covers 2272,1,4⟩,⟨.covers 928,1,2⟩,⟨.covers 1696,1,7⟩,⟨.covers 1472,1,2⟩]
def bound : Int := 20

theorem column_mask : listMask columns = restrictMask universeMask Source65.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source65.rootCodes link65 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual65_007
