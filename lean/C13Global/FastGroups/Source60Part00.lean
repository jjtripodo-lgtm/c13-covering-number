import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source60
namespace C13.Global.FastDual60_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,5,7]
def points : Finset C13.Point := {1,3,5,7}
def columns : List Code := [381,471,829,892,967,979,1143,1245,1367,1371,1373,1374,1397,1461,1493,1509,1639,1654,1693,1753,1821,1845,1852,1863,1875,1877,1878,1881,1882,1884,1893,1894,1908,1941,1945,1957,1987,1989,2001,2413,2425,2455,2518,2731,2734,2746,2794,2861,2873,2876,2901,2921,2924,2936,2951,2963,2966,2986,3011,3014,3026,3127,3187,3277,3292,3351,3379,3381,3405,3411,3413,3414,3417,3418,3420,3429,3433,3441,3477,3478,3493,3525,3532,3540,3623,3635,3638,3669,3683,3686,3698,3725,3737,3740,3754,3785,3788,3800,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 39,1,2⟩,⟨.covers 135,1,4⟩,⟨.covers 519,1,5⟩,⟨.covers 2055,1,4⟩,⟨.covers 43,1,19⟩,⟨.covers 75,1,19⟩,⟨.covers 147,1,8⟩,⟨.covers 99,1,4⟩,⟨.covers 1539,1,4⟩,⟨.covers 45,1,5⟩,⟨.covers 141,1,1⟩,⟨.covers 525,1,4⟩,⟨.covers 2061,1,4⟩,⟨.covers 57,1,3⟩,⟨.covers 201,1,12⟩,⟨.covers 2577,1,8⟩,⟨.covers 2337,1,2⟩,⟨.covers 3105,1,1⟩,⟨.covers 2625,1,2⟩,⟨.covers 897,1,1⟩,⟨.covers 3329,1,4⟩,⟨.covers 46,1,19⟩,⟨.covers 78,1,19⟩,⟨.covers 54,1,11⟩,⟨.covers 198,1,2⟩,⟨.covers 774,1,1⟩,⟨.covers 58,1,19⟩,⟨.covers 106,1,19⟩,⟨.covers 3082,1,11⟩,⟨.covers 114,1,2⟩,⟨.covers 210,1,5⟩,⟨.covers 2322,1,1⟩,⟨.covers 3090,1,1⟩,⟨.covers 1570,1,2⟩,⟨.covers 834,1,4⟩,⟨.covers 156,1,5⟩,⟨.covers 108,1,7⟩,⟨.covers 2316,1,1⟩,⟨.covers 1548,1,5⟩,⟨.covers 180,1,19⟩,⟨.covers 228,1,19⟩,⟨.covers 804,1,3⟩,⟨.covers 1572,1,1⟩,⟨.covers 2628,1,8⟩,⟨.covers 2436,1,3⟩,⟨.covers 3204,1,1⟩,⟨.covers 120,1,5⟩,⟨.covers 216,1,1⟩,⟨.covers 792,1,5⟩,⟨.covers 1560,1,2⟩,⟨.covers 1672,1,3⟩,⟨.covers 2160,1,8⟩,⟨.covers 2352,1,1⟩,⟨.covers 1584,1,3⟩,⟨.covers 2256,1,9⟩,⟨.covers 912,1,1⟩,⟨.covers 3216,1,4⟩,⟨.covers 3168,1,3⟩,⟨.covers 2464,1,8⟩,⟨.covers 1696,1,3⟩,⟨.covers 1728,1,2⟩,⟨.covers 1856,1,4⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_000
namespace C13.Global.FastDual60_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,5,10]
def points : Finset C13.Point := {1,3,5,10}
def columns : List Code := [254,381,471,508,829,892,956,967,979,981,982,1143,1245,1270,1371,1374,1461,1497,1498,1500,1509,1524,1639,1654,1693,1753,1756,1766,1882,1894,1945,1957,2008,2020,2298,2413,2425,2455,2515,2517,2518,2537,2552,2731,2734,2746,2773,2794,2861,2873,2876,2901,2921,2924,2936,2951,2963,2965,2966,2985,2986,2988,3000,3011,3013,3014,3025,3026,3028,3048,3127,3187,3251,3277,3289,3292,3314,3379,3418,3493,3505,3532,3544,3568,3623,3635,3686,3698,3725,3737,3788,3800,3851,3875,3914,3938,3977,4001,4040,4064]
def rows : List LinearRow := [⟨.covers 43,1,33⟩,⟨.covers 75,1,33⟩,⟨.covers 147,1,17⟩,⟨.covers 99,1,33⟩,⟨.covers 526,1,33⟩,⟨.covers 1038,1,17⟩,⟨.covers 774,1,17⟩,⟨.covers 1286,1,17⟩,⟨.covers 3078,1,33⟩,⟨.covers 778,1,33⟩,⟨.covers 178,1,17⟩,⟨.covers 2322,1,17⟩,⟨.covers 226,1,17⟩,⟨.covers 706,1,17⟩,⟨.covers 1584,1,33⟩,⟨.incident 1,8,-33⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_001
namespace C13.Global.FastDual60_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,5,11]
def points : Finset C13.Point := {1,3,5,11}
def columns : List Code := [254,381,471,508,829,892,956,967,979,981,982,1143,1245,1270,1367,1371,1373,1374,1397,1461,1491,1493,1494,1497,1498,1500,1509,1524,1639,1654,1693,1749,1753,1756,1766,1821,1845,1852,1863,1875,1877,1878,1881,1882,1884,1893,1894,1908,1941,1945,1948,1957,1972,1987,1989,1990,2001,2002,2004,2008,2020,2298,2413,2425,2455,2517,2518,2537,2552,2731,2734,2746,2773,2794,2901,2921,2966,2986,3028,3048,3127,3187,3251,3277,3285,3292,3314,3351,3379,3405,3413,3433,3441,3478,3532,3540,3568,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 135,1,1⟩,⟨.covers 43,1,2⟩,⟨.covers 75,1,2⟩,⟨.covers 147,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 1038,1,2⟩,⟨.covers 2566,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 2314,1,2⟩,⟨.covers 3082,1,2⟩,⟨.covers 226,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 2608,1,1⟩,⟨.covers 2656,1,1⟩,⟨.incident 1,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_002
namespace C13.Global.FastDual60_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,10]
def points : Finset C13.Point := {1,3,6,10}
def columns : List Code := [701,743,829,949,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1766,1882,1894,1906,1945,1957,1969,2231,2285,2413,2425,2455,2483,2485,2486,2537,2677,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2773,2789,2861,2869,2873,2876,2901,2917,2921,2929,2951,2963,2965,2966,2979,2981,2982,2985,2986,2988,2993,2994,2996,3000,3011,3013,3025,3041,3127,3251,3253,3277,3292,3308,3379,3418,3493,3505,3532,3544,3623,3635,3686,3725,3737,3749,3761,3788,3812,3851,3875,3914,3938,3977,4001,4040,4064]
def rows : List LinearRow := [⟨.covers 43,1,2⟩,⟨.covers 75,1,1⟩,⟨.covers 83,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 46,1,2⟩,⟨.covers 78,1,2⟩,⟨.covers 390,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 3078,1,2⟩,⟨.covers 58,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 202,1,2⟩,⟨.covers 178,1,1⟩,⟨.covers 226,1,2⟩,⟨.covers 3330,1,2⟩,⟨.covers 1616,1,2⟩,⟨.incident 1,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_003
namespace C13.Global.FastDual60_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,11]
def points : Finset C13.Point := {1,3,6,11}
def columns : List Code := [701,743,829,949,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1724,1766,1821,1845,1849,1852,1863,1875,1878,1882,1891,1894,1906,1941,1945,1948,1957,1969,1972,1976,1987,1990,2002,2018,2231,2285,2413,2425,2455,2483,2486,2537,2677,2731,2734,2739,2742,2746,2773,2901,2921,2929,2966,2986,2994,3127,3251,3254,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 43,1,14⟩,⟨.covers 75,1,12⟩,⟨.covers 83,1,1⟩,⟨.covers 147,1,6⟩,⟨.covers 99,1,4⟩,⟨.covers 2307,1,2⟩,⟨.covers 1539,1,2⟩,⟨.covers 525,1,1⟩,⟨.covers 1061,1,2⟩,⟨.covers 57,1,3⟩,⟨.covers 89,1,1⟩,⟨.covers 201,1,9⟩,⟨.covers 777,1,3⟩,⟨.covers 3081,1,2⟩,⟨.covers 3105,1,1⟩,⟨.covers 449,1,2⟩,⟨.covers 1665,1,3⟩,⟨.covers 3585,1,7⟩,⟨.covers 46,1,14⟩,⟨.covers 78,1,13⟩,⟨.covers 54,1,2⟩,⟨.covers 198,1,2⟩,⟨.covers 774,1,6⟩,⟨.covers 3078,1,4⟩,⟨.covers 154,1,8⟩,⟨.covers 106,1,14⟩,⟨.covers 778,1,9⟩,⟨.covers 3082,1,12⟩,⟨.covers 178,1,2⟩,⟨.covers 226,1,3⟩,⟨.covers 1794,1,2⟩,⟨.covers 3330,1,3⟩,⟨.covers 92,1,1⟩,⟨.covers 156,1,3⟩,⟨.covers 108,1,2⟩,⟨.covers 2316,1,9⟩,⟨.covers 1548,1,3⟩,⟨.covers 116,1,7⟩,⟨.covers 308,1,3⟩,⟨.covers 1124,1,1⟩,⟨.covers 2436,1,2⟩,⟨.covers 184,1,3⟩,⟨.covers 216,1,7⟩,⟨.covers 1800,1,3⟩,⟨.covers 2824,1,6⟩,⟨.covers 3592,1,2⟩,⟨.covers 1200,1,1⟩,⟨.covers 2384,1,7⟩,⟨.covers 912,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 1248,1,3⟩,⟨.covers 3168,1,4⟩,⟨.covers 1824,1,1⟩,⟨.covers 3360,1,3⟩,⟨.covers 2752,1,6⟩,⟨.incident 1,8,-3⟩,⟨.incident 3,8,-4⟩]
def bound : Int := 8

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_004
namespace C13.Global.FastDual60_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,10]
def points : Finset C13.Point := {1,3,7,10}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1371,1374,1395,1398,1402,1461,1509,1639,1651,1654,1693,1721,1753,1882,1894,1906,1945,1957,1969,2413,2421,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2861,2869,2873,2876,2901,2917,2921,2924,2929,2932,2936,2951,2963,2966,2979,2982,2986,2994,3011,3014,3026,3042,3127,3187,3190,3277,3292,3308,3379,3418,3442,3493,3532,3556,3623,3635,3686,3698,3725,3737,3788,3800,3851,3875,3914,3938,3977,4001,4040,4064]
def rows : List LinearRow := [⟨.covers 43,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 57,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 58,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3216,1,1⟩,⟨.incident 3,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_005
namespace C13.Global.FastDual60_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,11]
def points : Finset C13.Point := {1,3,7,11}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1651,1653,1654,1693,1721,1753,1821,1845,1849,1852,1863,1875,1877,1878,1881,1882,1884,1891,1893,1894,1905,1906,1908,1912,1941,1945,1957,1969,1987,1989,2001,2017,2413,2421,2425,2455,2486,2518,2677,2731,2734,2746,2794,2901,2921,2929,2966,2986,2994,3127,3187,3189,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 519,1,3⟩,⟨.covers 2055,1,11⟩,⟨.covers 75,1,11⟩,⟨.covers 99,1,5⟩,⟨.covers 163,1,5⟩,⟨.covers 525,1,3⟩,⟨.covers 2061,1,11⟩,⟨.covers 57,1,5⟩,⟨.covers 169,1,5⟩,⟨.covers 2817,1,11⟩,⟨.covers 3585,1,8⟩,⟨.covers 46,1,11⟩,⟨.covers 78,1,11⟩,⟨.covers 774,1,8⟩,⟨.covers 154,1,8⟩,⟨.covers 202,1,11⟩,⟨.covers 778,1,11⟩,⟨.covers 3082,1,11⟩,⟨.covers 114,1,5⟩,⟨.covers 210,1,11⟩,⟨.covers 1548,1,8⟩,⟨.covers 180,1,11⟩,⟨.covers 564,1,3⟩,⟨.covers 228,1,11⟩,⟨.covers 612,1,3⟩,⟨.covers 120,1,5⟩,⟨.covers 216,1,11⟩,⟨.covers 2704,1,3⟩,⟨.covers 3360,1,11⟩,⟨.covers 3648,1,3⟩,⟨.covers 1920,1,11⟩,⟨.covers 3456,1,11⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_006
namespace C13.Global.FastDual60_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,5,6,10]
def points : Finset C13.Point := {1,5,6,10}
def columns : List Code := [445,475,829,925,941,956,967,971,979,1371,1374,1437,1453,1461,1498,1639,1646,1654,1693,1766,1870,1882,1894,1933,1945,1957,2235,2269,2365,2397,2413,2425,2455,2459,2461,2462,2477,2489,2509,2521,2537,2653,2717,2731,2734,2746,2765,2773,2845,2861,2873,2876,2893,2901,2905,2921,2951,2955,2957,2958,2963,2965,2966,2969,2970,2972,2985,2986,2988,3000,3011,3013,3017,3025,3127,3131,3229,3251,3277,3292,3355,3379,3418,3469,3481,3493,3505,3532,3544,3623,3635,3686,3725,3737,3788,3851,3875,3914,3938,3977,4001,4040,4064]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 43,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 99,1,2⟩,⟨.covers 163,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 197,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 106,1,2⟩,⟨.covers 114,1,2⟩,⟨.covers 226,1,2⟩,⟨.covers 3330,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 120,1,2⟩,⟨.covers 232,1,2⟩,⟨.covers 1200,1,1⟩,⟨.covers 1328,1,1⟩,⟨.covers 2608,1,1⟩,⟨.covers 1232,1,1⟩,⟨.covers 848,1,1⟩,⟨.covers 3152,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 3648,1,1⟩,⟨.incident 5,8,-1⟩,⟨.incident 6,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_007
