import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source56
namespace C13.Global.FastDual56_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,3,5]
def points : Finset C13.Point := {1,2,3,5}
def columns : List Code := [254,508,829,892,956,979,1270,1371,1461,1491,1497,1498,1509,1524,1639,1654,1753,1766,1845,1852,1875,1881,1882,1893,1894,1908,1945,1957,1972,1987,2001,2002,2008,2020,2298,2425,2455,2515,2517,2518,2537,2552,2731,2746,2773,2794,2873,2876,2901,2921,2936,2963,2965,2966,2985,2986,3000,3011,3025,3026,3028,3048,3187,3251,3277,3285,3289,3292,3314,3379,3411,3417,3418,3433,3441,3475,3477,3478,3493,3505,3525,3529,3532,3537,3538,3540,3544,3553,3568,3635,3669,3683,3686,3698,3737,3747,3754,3762,3781,3785,3788,3793,3796,3800,3810,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 39,1,3⟩,⟨.covers 2055,1,4⟩,⟨.covers 43,1,3⟩,⟨.covers 1035,1,4⟩,⟨.covers 45,1,3⟩,⟨.covers 77,1,4⟩,⟨.covers 1073,1,1⟩,⟨.covers 2097,1,1⟩,⟨.covers 353,1,1⟩,⟨.covers 2145,1,1⟩,⟨.covers 417,1,1⟩,⟨.covers 1185,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 3090,1,1⟩,⟨.covers 450,1,2⟩,⟨.covers 706,1,1⟩,⟨.covers 834,1,2⟩,⟨.covers 898,1,2⟩,⟨.covers 596,1,1⟩,⟨.covers 2132,1,2⟩,⟨.covers 2580,1,2⟩,⟨.covers 2628,1,2⟩,⟨.covers 1412,1,1⟩,⟨.covers 664,1,1⟩,⟨.covers 1176,1,2⟩,⟨.covers 1560,1,2⟩,⟨.covers 2376,1,1⟩,⟨.covers 1672,1,2⟩,⟨.covers 368,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 432,1,1⟩,⟨.covers 2224,1,1⟩,⟨.covers 1584,1,1⟩,⟨.covers 2608,1,1⟩,⟨.covers 1248,1,1⟩,⟨.covers 2272,1,1⟩,⟨.covers 864,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 928,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 3360,1,2⟩,⟨.incident 1,8,3⟩,⟨.incident 2,8,3⟩,⟨.incident 3,8,3⟩,⟨.incident 5,8,1⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source56.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source56.rootCodes link56 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual56_000
namespace C13.Global.FastDual56_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,5,10]
def points : Finset C13.Point := {1,2,5,10}
def columns : List Code := [254,445,475,508,829,892,956,971,979,985,986,1270,1371,1453,1461,1497,1498,1509,1524,1639,1646,1654,1753,1766,1882,1894,1945,1957,2008,2020,2235,2269,2298,2425,2455,2459,2461,2462,2489,2515,2517,2518,2521,2522,2524,2537,2552,2653,2731,2746,2773,2777,2780,2794,2845,2873,2876,2901,2905,2908,2921,2936,2955,2963,2965,2966,2969,2970,2972,2985,2986,3000,3011,3017,3018,3025,3026,3028,3032,3048,3131,3187,3251,3277,3289,3292,3314,3355,3379,3418,3469,3481,3493,3505,3532,3544,3568,3635,3686,3698,3737,3788,3800,3854,3866,3878,3890,3980,3992,4004,4016]
def rows : List LinearRow := [⟨.covers 39,1,13⟩,⟨.covers 135,1,71⟩,⟨.covers 43,1,7⟩,⟨.covers 75,1,9⟩,⟨.covers 1035,1,13⟩,⟨.covers 2059,1,7⟩,⟨.covers 163,1,27⟩,⟨.covers 1283,1,27⟩,⟨.covers 45,1,22⟩,⟨.covers 77,1,9⟩,⟨.covers 1037,1,7⟩,⟨.covers 53,1,22⟩,⟨.covers 3077,1,29⟩,⟨.covers 1073,1,7⟩,⟨.covers 2129,1,4⟩,⟨.covers 1553,1,22⟩,⟨.covers 2577,1,4⟩,⟨.covers 353,1,18⟩,⟨.covers 2145,1,16⟩,⟨.covers 449,1,9⟩,⟨.covers 1665,1,29⟩,⟨.covers 142,1,29⟩,⟨.covers 2062,1,27⟩,⟨.covers 1098,1,9⟩,⟨.covers 2186,1,7⟩,⟨.covers 450,1,40⟩,⟨.covers 898,1,33⟩,⟨.covers 556,1,2⟩,⟨.covers 1100,1,2⟩,⟨.covers 2188,1,7⟩,⟨.covers 2132,1,31⟩,⟨.covers 2580,1,38⟩,⟨.covers 184,1,4⟩,⟨.covers 568,1,2⟩,⟨.covers 664,1,2⟩,⟨.covers 1176,1,7⟩,⟨.covers 680,1,7⟩,⟨.covers 2344,1,7⟩,⟨.covers 1352,1,13⟩,⟨.covers 2376,1,2⟩,⟨.covers 3144,1,13⟩,⟨.covers 3336,1,24⟩,⟨.covers 368,1,22⟩,⟨.covers 848,1,9⟩,⟨.covers 1616,1,13⟩,⟨.covers 3152,1,7⟩,⟨.covers 1808,1,27⟩,⟨.covers 2272,1,18⟩,⟨.covers 864,1,13⟩,⟨.covers 2656,1,13⟩,⟨.covers 1472,1,2⟩,⟨.covers 1728,1,13⟩,⟨.covers 2752,1,9⟩,⟨.covers 3712,1,22⟩,⟨.incident 1,8,16⟩,⟨.incident 2,8,20⟩,⟨.incident 5,8,38⟩,⟨.incident 10,8,20⟩]
def bound : Int := 109

theorem column_mask : listMask columns = restrictMask universeMask Source56.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source56.rootCodes link56 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual56_001
namespace C13.Global.FastDual56_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,5,11]
def points : Finset C13.Point := {1,2,5,11}
def columns : List Code := [254,445,475,508,829,892,956,971,979,985,986,1270,1371,1453,1461,1491,1497,1498,1509,1524,1639,1646,1654,1753,1766,1837,1845,1852,1867,1875,1881,1882,1893,1894,1900,1908,1945,1957,1964,1972,1987,1993,1994,2001,2002,2008,2020,2235,2269,2298,2425,2455,2462,2517,2518,2524,2537,2552,2653,2731,2746,2773,2780,2794,2901,2921,2966,2986,3028,3048,3131,3187,3251,3277,3285,3292,3314,3379,3433,3441,3478,3532,3540,3568,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 83,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 2307,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 2062,1,1⟩,⟨.covers 54,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 2608,1,1⟩,⟨.incident 1,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source56.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source56.rootCodes link56 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual56_002
namespace C13.Global.FastDual56_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,7,11]
def points : Finset C13.Point := {1,2,7,11}
def columns : List Code := [637,747,829,885,889,892,971,979,995,1147,1261,1371,1395,1401,1402,1453,1461,1509,1639,1643,1645,1646,1651,1653,1654,1657,1658,1660,1721,1753,1769,1837,1845,1849,1852,1867,1875,1881,1882,1891,1893,1894,1897,1898,1900,1905,1906,1908,1912,1945,1957,1961,1969,1987,1993,2001,2017,2425,2455,2462,2486,2518,2653,2677,2681,2731,2746,2794,2901,2921,2929,2966,2986,2994,3131,3187,3193,3277,3292,3308,3379,3433,3441,3478,3532,3540,3627,3635,3661,3669,3689,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 135,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 1232,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 480,1,1⟩,⟨.covers 2272,1,1⟩,⟨.covers 2848,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source56.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source56.rootCodes link56 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual56_003
namespace C13.Global.FastDual56_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,5,7]
def points : Finset C13.Point := {1,3,5,7}
def columns : List Code := [381,471,829,892,967,979,1143,1245,1367,1371,1373,1374,1397,1461,1493,1509,1639,1654,1693,1753,1821,1845,1852,1863,1875,1877,1878,1881,1882,1884,1893,1894,1908,1941,1945,1957,1987,1989,2001,2413,2425,2455,2518,2731,2734,2746,2794,2861,2873,2876,2901,2921,2924,2936,2951,2963,2966,2986,3011,3014,3026,3127,3187,3277,3292,3351,3379,3381,3405,3411,3413,3414,3417,3418,3420,3429,3433,3441,3477,3478,3493,3525,3532,3540,3623,3635,3638,3669,3683,3686,3698,3725,3737,3740,3754,3785,3788,3800,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 135,1,5⟩,⟨.covers 519,1,4⟩,⟨.covers 2055,1,4⟩,⟨.covers 43,1,19⟩,⟨.covers 75,1,19⟩,⟨.covers 147,1,7⟩,⟨.covers 99,1,5⟩,⟨.covers 2307,1,1⟩,⟨.covers 1539,1,5⟩,⟨.covers 45,1,4⟩,⟨.covers 141,1,2⟩,⟨.covers 525,1,5⟩,⟨.covers 2061,1,4⟩,⟨.covers 57,1,2⟩,⟨.covers 201,1,11⟩,⟨.covers 777,1,1⟩,⟨.covers 2577,1,8⟩,⟨.covers 2337,1,3⟩,⟨.covers 3105,1,1⟩,⟨.covers 897,1,3⟩,⟨.covers 1665,1,1⟩,⟨.covers 46,1,19⟩,⟨.covers 78,1,19⟩,⟨.covers 54,1,12⟩,⟨.covers 198,1,3⟩,⟨.covers 58,1,19⟩,⟨.covers 106,1,19⟩,⟨.covers 3082,1,11⟩,⟨.covers 114,1,1⟩,⟨.covers 210,1,5⟩,⟨.covers 1570,1,3⟩,⟨.covers 834,1,5⟩,⟨.covers 1602,1,2⟩,⟨.covers 156,1,4⟩,⟨.covers 108,1,8⟩,⟨.covers 1548,1,4⟩,⟨.covers 180,1,19⟩,⟨.covers 2580,1,2⟩,⟨.covers 228,1,19⟩,⟨.covers 804,1,1⟩,⟨.covers 2628,1,8⟩,⟨.covers 2436,1,2⟩,⟨.covers 3204,1,1⟩,⟨.covers 1796,1,3⟩,⟨.covers 3332,1,2⟩,⟨.covers 120,1,5⟩,⟨.covers 216,1,2⟩,⟨.covers 792,1,4⟩,⟨.covers 2376,1,1⟩,⟨.covers 3144,1,1⟩,⟨.covers 1672,1,2⟩,⟨.covers 2160,1,9⟩,⟨.covers 1584,1,2⟩,⟨.covers 2256,1,8⟩,⟨.covers 3216,1,3⟩,⟨.covers 1808,1,1⟩,⟨.covers 3344,1,3⟩,⟨.covers 864,1,1⟩,⟨.covers 3168,1,4⟩,⟨.covers 928,1,11⟩,⟨.covers 2496,1,1⟩,⟨.covers 1728,1,3⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source56.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source56.rootCodes link56 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual56_004
namespace C13.Global.FastDual56_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,5,10]
def points : Finset C13.Point := {1,3,5,10}
def columns : List Code := [254,381,471,508,829,892,956,967,979,981,982,1143,1245,1270,1371,1374,1461,1497,1498,1500,1509,1524,1639,1654,1693,1753,1756,1766,1882,1894,1945,1957,2008,2020,2298,2413,2425,2455,2515,2517,2518,2537,2552,2731,2734,2746,2773,2794,2861,2873,2876,2901,2921,2924,2936,2951,2963,2965,2966,2985,2986,2988,3000,3011,3013,3014,3025,3026,3028,3048,3127,3187,3251,3277,3289,3292,3314,3379,3418,3493,3505,3532,3544,3568,3623,3635,3686,3698,3725,3737,3788,3800,3854,3866,3878,3890,3980,3992,4004,4016]
def rows : List LinearRow := [⟨.covers 39,1,2⟩,⟨.covers 135,1,2⟩,⟨.covers 2055,1,1⟩,⟨.covers 43,1,2⟩,⟨.covers 75,1,3⟩,⟨.covers 147,1,2⟩,⟨.covers 99,1,1⟩,⟨.covers 2307,1,2⟩,⟨.covers 45,1,3⟩,⟨.covers 141,1,2⟩,⟨.covers 525,1,2⟩,⟨.covers 57,1,1⟩,⟨.covers 3081,1,2⟩,⟨.covers 1553,1,2⟩,⟨.covers 2145,1,2⟩,⟨.covers 417,1,1⟩,⟨.covers 1185,1,1⟩,⟨.covers 1313,1,1⟩,⟨.covers 1409,1,1⟩,⟨.covers 1038,1,2⟩,⟨.covers 3082,1,2⟩,⟨.covers 450,1,3⟩,⟨.covers 898,1,2⟩,⟨.covers 172,1,2⟩,⟨.covers 1100,1,1⟩,⟨.covers 2132,1,4⟩,⟨.covers 2580,1,5⟩,⟨.covers 420,1,1⟩,⟨.covers 2628,1,2⟩,⟨.covers 3140,1,1⟩,⟨.covers 664,1,2⟩,⟨.covers 2376,1,1⟩,⟨.covers 3144,1,1⟩,⟨.covers 368,1,2⟩,⟨.covers 432,1,1⟩,⟨.covers 1584,1,2⟩,⟨.covers 1616,1,1⟩,⟨.covers 1808,1,2⟩,⟨.covers 1248,1,1⟩,⟨.covers 2272,1,2⟩,⟨.covers 864,1,3⟩,⟨.covers 1696,1,1⟩,⟨.covers 1728,1,2⟩,⟨.covers 3456,1,1⟩,⟨.covers 3712,1,1⟩,⟨.incident 1,8,4⟩,⟨.incident 3,8,3⟩,⟨.incident 5,8,3⟩,⟨.incident 10,8,1⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source56.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source56.rootCodes link56 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual56_005
namespace C13.Global.FastDual56_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,5,11]
def points : Finset C13.Point := {1,3,5,11}
def columns : List Code := [254,381,471,508,829,892,956,967,979,981,982,1143,1245,1270,1367,1371,1373,1374,1397,1461,1491,1493,1494,1497,1498,1500,1509,1524,1639,1654,1693,1749,1753,1756,1766,1821,1845,1852,1863,1875,1877,1878,1881,1882,1884,1893,1894,1908,1941,1945,1948,1957,1972,1987,1989,1990,2001,2002,2004,2008,2020,2298,2413,2425,2455,2517,2518,2537,2552,2731,2734,2746,2773,2794,2901,2921,2966,2986,3028,3048,3127,3187,3251,3277,3285,3292,3314,3351,3379,3405,3413,3433,3441,3478,3532,3540,3568,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 39,1,8⟩,⟨.covers 135,1,4⟩,⟨.covers 519,1,4⟩,⟨.covers 43,1,17⟩,⟨.covers 75,1,17⟩,⟨.covers 147,1,10⟩,⟨.covers 99,1,2⟩,⟨.covers 45,1,7⟩,⟨.covers 141,1,5⟩,⟨.covers 525,1,2⟩,⟨.covers 57,1,3⟩,⟨.covers 201,1,9⟩,⟨.covers 2097,1,1⟩,⟨.covers 417,1,3⟩,⟨.covers 1185,1,2⟩,⟨.covers 2337,1,1⟩,⟨.covers 1665,1,3⟩,⟨.covers 526,1,17⟩,⟨.covers 1038,1,17⟩,⟨.covers 54,1,2⟩,⟨.covers 774,1,3⟩,⟨.covers 3078,1,3⟩,⟨.covers 154,1,2⟩,⟨.covers 2314,1,17⟩,⟨.covers 3082,1,17⟩,⟨.covers 114,1,2⟩,⟨.covers 226,1,3⟩,⟨.covers 706,1,4⟩,⟨.covers 1794,1,7⟩,⟨.covers 3330,1,11⟩,⟨.covers 108,1,4⟩,⟨.covers 2316,1,1⟩,⟨.covers 1548,1,3⟩,⟨.covers 564,1,2⟩,⟨.covers 228,1,3⟩,⟨.covers 420,1,4⟩,⟨.covers 2820,1,11⟩,⟨.covers 3588,1,11⟩,⟨.covers 664,1,2⟩,⟨.covers 232,1,1⟩,⟨.covers 1800,1,6⟩,⟨.covers 3336,1,12⟩,⟨.covers 2160,1,8⟩,⟨.covers 432,1,3⟩,⟨.covers 2608,1,12⟩,⟨.covers 1808,1,3⟩,⟨.covers 864,1,4⟩,⟨.covers 2656,1,9⟩,⟨.incident 1,8,-3⟩,⟨.incident 3,8,-3⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source56.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source56.rootCodes link56 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual56_006
namespace C13.Global.FastDual56_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,10]
def points : Finset C13.Point := {1,3,7,10}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1371,1374,1395,1398,1402,1461,1509,1639,1651,1654,1693,1721,1753,1882,1894,1906,1945,1957,1969,2413,2421,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2861,2869,2873,2876,2901,2917,2921,2924,2929,2932,2936,2951,2963,2966,2979,2982,2986,2994,3011,3014,3026,3042,3127,3187,3190,3277,3292,3308,3379,3418,3442,3493,3532,3556,3623,3635,3686,3698,3725,3737,3788,3800,3854,3866,3878,3890,3980,3992,4004,4016]
def rows : List LinearRow := [⟨.covers 43,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 1728,1,1⟩,⟨.incident 3,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source56.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source56.rootCodes link56 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual56_007
