import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source40
namespace C13.Global.FastDual40_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,8,11]
def points : Finset C13.Point := {1,2,8,11}
def columns : List Code := [247,251,253,254,445,475,499,501,502,505,506,508,637,747,755,757,758,761,762,764,829,889,892,949,956,971,979,986,995,1001,1009,1010,1012,1016,1147,1261,1267,1269,1270,1273,1274,1276,1371,1401,1402,1453,1461,1468,1491,1498,1509,1513,1521,1522,1524,1528,1639,1643,1645,1646,1651,1653,1654,1657,1658,1660,1721,1753,1763,1765,1766,1769,1770,1772,1777,1778,1780,1784,1837,1852,1867,1882,1897,1912,1957,1972,1987,2002,2017,2032,2235,2269,2291,2293,2294,2297,2298,2300,2425,2455,2462,2486,2518,2537,2545,2546,2548,2552,2653,2677,2681,2731,2739,2746,2773,2780,2793,2794,2801,2802,2804,2808,2921,2966,3056,3131,3187,3193,3251,3258,3277,3285,3292,3305,3308,3313,3314,3316,3320,3433,3478,3568,3627,3635,3661,3669,3689,3697,3754,3762,3788,3796,3816,3824]
def rows : List LinearRow := [⟨.covers 263,1,21⟩,⟨.covers 519,1,20⟩,⟨.covers 139,1,9⟩,⟨.covers 267,1,1⟩,⟨.covers 2059,1,4⟩,⟨.covers 83,1,2⟩,⟨.covers 163,1,4⟩,⟨.covers 1283,1,9⟩,⟨.covers 2563,1,4⟩,⟨.covers 141,1,8⟩,⟨.covers 269,1,4⟩,⟨.covers 2061,1,1⟩,⟨.covers 197,1,2⟩,⟨.covers 773,1,5⟩,⟨.covers 3077,1,7⟩,⟨.covers 2097,1,4⟩,⟨.covers 2129,1,2⟩,⟨.covers 657,1,7⟩,⟨.covers 417,1,1⟩,⟨.covers 449,1,1⟩,⟨.covers 270,1,21⟩,⟨.covers 526,1,20⟩,⟨.covers 166,1,12⟩,⟨.covers 774,1,21⟩,⟨.covers 1286,1,21⟩,⟨.covers 202,1,1⟩,⟨.covers 778,1,8⟩,⟨.covers 3082,1,7⟩,⟨.covers 1074,1,6⟩,⟨.covers 338,1,6⟩,⟨.covers 1106,1,2⟩,⟨.covers 1794,1,1⟩,⟨.covers 3586,1,6⟩,⟨.covers 92,1,3⟩,⟨.covers 1292,1,4⟩,⟨.covers 2572,1,9⟩,⟨.covers 564,1,4⟩,⟨.covers 596,1,1⟩,⟨.covers 2132,1,2⟩,⟨.covers 1796,1,4⟩,⟨.covers 3588,1,1⟩,⟨.covers 312,1,4⟩,⟨.covers 664,1,2⟩,⟨.covers 1176,1,7⟩,⟨.covers 232,1,4⟩,⟨.covers 2824,1,18⟩,⟨.covers 3336,1,18⟩,⟨.covers 624,1,1⟩,⟨.covers 1328,1,2⟩,⟨.covers 2352,1,8⟩,⟨.covers 2608,1,1⟩,⟨.covers 848,1,3⟩,⟨.covers 3152,1,5⟩,⟨.covers 736,1,2⟩,⟨.covers 3232,1,1⟩,⟨.covers 2496,1,2⟩,⟨.covers 1856,1,1⟩,⟨.covers 1920,1,8⟩,⟨.covers 3712,1,7⟩,⟨.incident 1,8,-3⟩]
def bound : Int := 18

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_008
namespace C13.Global.FastDual40_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,8]
def points : Finset C13.Point := {1,3,6,8}
def columns : List Code := [254,506,701,743,758,829,949,956,967,979,995,1010,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1724,1766,1852,1882,1957,1972,1987,2002,2231,2285,2300,2413,2425,2455,2485,2486,2537,2552,2677,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2773,2789,2804,2861,2876,2921,2951,2966,2981,2996,3011,3041,3056,3127,3251,3253,3254,3277,3292,3308,3418,3433,3448,3478,3493,3508,3623,3635,3637,3638,3669,3685,3686,3700,3725,3733,3737,3740,3747,3749,3750,3753,3754,3756,3761,3762,3764,3768,3781,3788,3796,3812,3854,3884,3914,3944,3974,4004,4034,4064]
def rows : List LinearRow := [⟨.covers 71,1,8⟩,⟨.covers 263,1,20⟩,⟨.covers 1031,1,9⟩,⟨.covers 75,1,13⟩,⟨.covers 139,1,72⟩,⟨.covers 99,1,28⟩,⟨.covers 2307,1,23⟩,⟨.covers 77,1,9⟩,⟨.covers 269,1,14⟩,⟨.covers 1037,1,9⟩,⟨.covers 2061,1,4⟩,⟨.covers 201,1,25⟩,⟨.covers 777,1,27⟩,⟨.covers 2097,1,3⟩,⟨.covers 593,1,26⟩,⟨.covers 2129,1,23⟩,⟨.covers 657,1,1⟩,⟨.covers 1313,1,16⟩,⟨.covers 3105,1,5⟩,⟨.covers 449,1,2⟩,⟨.covers 2369,1,5⟩,⟨.covers 1409,1,17⟩,⟨.covers 1665,1,7⟩,⟨.covers 142,1,26⟩,⟨.covers 526,1,28⟩,⟨.covers 278,1,5⟩,⟨.covers 550,1,7⟩,⟨.covers 2182,1,2⟩,⟨.covers 2098,1,37⟩,⟨.covers 3106,1,34⟩,⟨.covers 284,1,7⟩,⟨.covers 556,1,2⟩,⟨.covers 2188,1,7⟩,⟨.covers 788,1,6⟩,⟨.covers 2324,1,3⟩,⟨.covers 2580,1,2⟩,⟨.covers 228,1,22⟩,⟨.covers 1124,1,13⟩,⟨.covers 420,1,5⟩,⟨.covers 1188,1,7⟩,⟨.covers 1220,1,13⟩,⟨.covers 2628,1,5⟩,⟨.covers 2820,1,9⟩,⟨.covers 664,1,35⟩,⟨.covers 1672,1,38⟩,⟨.covers 624,1,23⟩,⟨.covers 1328,1,13⟩,⟨.covers 1584,1,9⟩,⟨.covers 2256,1,25⟩,⟨.covers 1616,1,13⟩,⟨.covers 3152,1,13⟩,⟨.covers 1424,1,13⟩,⟨.covers 3216,1,9⟩,⟨.covers 3168,1,5⟩,⟨.covers 1824,1,19⟩,⟨.covers 1728,1,3⟩,⟨.covers 3456,1,21⟩,⟨.incident 1,8,18⟩,⟨.incident 3,8,16⟩,⟨.incident 6,8,24⟩,⟨.incident 8,8,35⟩]
def bound : Int := 107

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_009
namespace C13.Global.FastDual40_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,9]
def points : Finset C13.Point := {1,3,6,9}
def columns : List Code := [254,506,701,743,758,829,953,956,967,979,995,1010,1371,1374,1402,1461,1498,1639,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2231,2285,2300,2413,2425,2455,2483,2485,2486,2537,2552,2677,2731,2734,2745,2746,2748,2773,2804,2876,2901,2986,3000,3011,3025,3056,3127,3251,3253,3254,3277,3292,3308,3351,3379,3381,3382,3405,3417,3418,3420,3433,3436,3448,3475,3477,3478,3493,3505,3506,3508,3529,3532,3544,3560,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 2055,1,6⟩,⟨.covers 75,1,6⟩,⟨.covers 139,1,25⟩,⟨.covers 83,1,19⟩,⟨.covers 147,1,6⟩,⟨.covers 99,1,25⟩,⟨.covers 2307,1,6⟩,⟨.covers 270,1,25⟩,⟨.covers 526,1,25⟩,⟨.covers 774,1,25⟩,⟨.covers 3078,1,6⟩,⟨.covers 202,1,25⟩,⟨.covers 2314,1,12⟩,⟨.covers 3082,1,6⟩,⟨.covers 1074,1,12⟩,⟨.covers 2194,1,6⟩,⟨.covers 2818,1,12⟩,⟨.covers 3330,1,6⟩,⟨.covers 3586,1,19⟩,⟨.covers 1728,1,25⟩,⟨.incident 1,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_010
namespace C13.Global.FastDual40_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,11]
def points : Finset C13.Point := {1,3,6,11}
def columns : List Code := [254,506,701,743,758,829,949,953,956,967,979,995,1010,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1724,1766,1821,1845,1849,1852,1863,1875,1878,1882,1891,1894,1906,1941,1945,1948,1957,1969,1972,1976,1987,1990,2002,2018,2231,2285,2300,2413,2425,2455,2483,2486,2537,2552,2677,2731,2734,2739,2742,2746,2773,2804,2901,2921,2929,2966,2986,2994,3056,3127,3251,3254,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 75,1,3⟩,⟨.covers 139,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 201,1,3⟩,⟨.covers 777,1,1⟩,⟨.covers 2569,1,2⟩,⟨.covers 270,1,3⟩,⟨.covers 526,1,3⟩,⟨.covers 202,1,2⟩,⟨.covers 2314,1,3⟩,⟨.covers 1546,1,2⟩,⟨.covers 2316,1,3⟩,⟨.covers 568,1,1⟩,⟨.covers 664,1,1⟩,⟨.covers 3168,1,3⟩,⟨.incident 3,8,-3⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_011
namespace C13.Global.FastDual40_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,8]
def points : Finset C13.Point := {1,3,7,8}
def columns : List Code := [381,471,829,889,892,967,979,995,1143,1245,1371,1374,1401,1402,1404,1461,1509,1639,1651,1653,1654,1693,1721,1753,1852,1882,1912,1957,1987,2017,2413,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2861,2876,2921,2936,2951,2966,3011,3026,3127,3187,3189,3190,3277,3292,3308,3418,3433,3448,3478,3493,3508,3623,3635,3637,3638,3669,3683,3685,3686,3697,3698,3700,3725,3737,3740,3753,3754,3756,3768,3785,3788,3800,3816,3854,3884,3914,3944,3974,4004,4034,4064]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,2⟩,⟨.covers 1283,1,1⟩,⟨.covers 2307,1,2⟩,⟨.covers 1539,1,1⟩,⟨.covers 78,1,2⟩,⟨.covers 142,1,2⟩,⟨.covers 198,1,2⟩,⟨.covers 106,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 178,1,2⟩,⟨.covers 3090,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 912,1,2⟩,⟨.incident 1,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_012
namespace C13.Global.FastDual40_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,9]
def points : Finset C13.Point := {1,3,7,9}
def columns : List Code := [381,471,829,885,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1653,1654,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2413,2421,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2876,2901,2932,2986,3011,3042,3127,3187,3189,3190,3277,3292,3308,3351,3379,3381,3382,3405,3411,3413,3414,3417,3418,3420,3429,3433,3436,3441,3442,3444,3448,3477,3478,3493,3508,3525,3532,3540,3556,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 519,1,10⟩,⟨.covers 2055,1,4⟩,⟨.covers 75,1,12⟩,⟨.covers 147,1,7⟩,⟨.covers 99,1,1⟩,⟨.covers 163,1,4⟩,⟨.covers 141,1,6⟩,⟨.covers 2061,1,3⟩,⟨.covers 169,1,7⟩,⟨.covers 297,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 777,1,10⟩,⟨.covers 3081,1,1⟩,⟨.covers 2097,1,3⟩,⟨.covers 417,1,4⟩,⟨.covers 2337,1,1⟩,⟨.covers 3105,1,1⟩,⟨.covers 2625,1,1⟩,⟨.covers 78,1,12⟩,⟨.covers 142,1,12⟩,⟨.covers 774,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 202,1,10⟩,⟨.covers 778,1,1⟩,⟨.covers 1546,1,12⟩,⟨.covers 114,1,6⟩,⟨.covers 178,1,1⟩,⟨.covers 210,1,4⟩,⟨.covers 226,1,1⟩,⟨.covers 2818,1,10⟩,⟨.covers 3330,1,6⟩,⟨.covers 156,1,4⟩,⟨.covers 108,1,4⟩,⟨.covers 2316,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 180,1,7⟩,⟨.covers 228,1,7⟩,⟨.covers 2820,1,10⟩,⟨.covers 3588,1,10⟩,⟨.covers 120,1,6⟩,⟨.covers 3336,1,6⟩,⟨.covers 624,1,1⟩,⟨.covers 2256,1,7⟩,⟨.covers 2704,1,10⟩,⟨.covers 1824,1,10⟩,⟨.covers 1728,1,10⟩,⟨.covers 1920,1,1⟩,⟨.covers 3456,1,4⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_013
namespace C13.Global.FastDual40_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,11]
def points : Finset C13.Point := {1,3,7,11}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1651,1653,1654,1693,1721,1753,1821,1845,1849,1852,1863,1875,1877,1878,1881,1882,1884,1891,1893,1894,1905,1906,1908,1912,1941,1945,1957,1969,1987,1989,2001,2017,2413,2421,2425,2455,2486,2518,2677,2731,2734,2746,2794,2901,2921,2929,2966,2986,2994,3127,3187,3189,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 135,1,2⟩,⟨.covers 519,1,4⟩,⟨.covers 2055,1,1⟩,⟨.covers 75,1,11⟩,⟨.covers 147,1,7⟩,⟨.covers 99,1,5⟩,⟨.covers 2307,1,1⟩,⟨.covers 2563,1,6⟩,⟨.covers 525,1,7⟩,⟨.covers 2061,1,9⟩,⟨.covers 169,1,4⟩,⟨.covers 201,1,2⟩,⟨.covers 777,1,3⟩,⟨.covers 78,1,11⟩,⟨.covers 142,1,6⟩,⟨.covers 198,1,2⟩,⟨.covers 774,1,4⟩,⟨.covers 2566,1,4⟩,⟨.covers 3078,1,9⟩,⟨.covers 154,1,6⟩,⟨.covers 106,1,1⟩,⟨.covers 202,1,6⟩,⟨.covers 2314,1,11⟩,⟨.covers 1546,1,6⟩,⟨.covers 3082,1,4⟩,⟨.covers 114,1,2⟩,⟨.covers 1074,1,1⟩,⟨.covers 226,1,4⟩,⟨.covers 1794,1,4⟩,⟨.covers 156,1,4⟩,⟨.covers 108,1,2⟩,⟨.covers 172,1,1⟩,⟨.covers 116,1,2⟩,⟨.covers 180,1,11⟩,⟨.covers 228,1,8⟩,⟨.covers 1572,1,2⟩,⟨.covers 2820,1,3⟩,⟨.covers 3588,1,6⟩,⟨.covers 120,1,6⟩,⟨.covers 184,1,4⟩,⟨.covers 216,1,5⟩,⟨.covers 1800,1,1⟩,⟨.covers 3336,1,2⟩,⟨.covers 2160,1,2⟩,⟨.covers 1584,1,2⟩,⟨.covers 2608,1,1⟩,⟨.covers 720,1,4⟩,⟨.covers 3216,1,2⟩,⟨.covers 480,1,2⟩,⟨.covers 1824,1,1⟩,⟨.covers 3360,1,8⟩,⟨.covers 2496,1,9⟩,⟨.covers 2880,1,7⟩,⟨.covers 3648,1,5⟩,⟨.covers 1920,1,7⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_014
namespace C13.Global.FastDual40_015
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,9,11]
def points : Finset C13.Point := {1,3,9,11}
def columns : List Code := [247,251,253,254,381,471,499,501,502,505,506,508,701,743,755,757,758,761,762,764,829,885,892,953,956,967,979,981,995,998,1009,1010,1012,1016,1143,1245,1267,1269,1270,1273,1274,1276,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1491,1493,1494,1497,1498,1500,1509,1521,1522,1524,1528,1639,1653,1654,1693,1721,1724,1749,1753,1763,1766,1777,1778,1780,1784,1821,1852,1863,1877,1894,1908,1945,1976,1987,2001,2018,2032,2231,2285,2291,2293,2294,2297,2298,2300,2413,2421,2425,2455,2483,2486,2517,2518,2537,2540,2545,2546,2548,2552,2677,2731,2734,2746,2773,2794,2801,2802,2804,2808,2901,2986,3056,3127,3187,3189,3251,3254,3277,3285,3292,3305,3308,3313,3314,3316,3320,3351,3379,3405,3413,3433,3441,3478,3506,3532,3540,3560,3568,3669,3754,3824]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 267,1,2⟩,⟨.covers 523,1,2⟩,⟨.covers 1539,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 417,1,1⟩,⟨.covers 270,1,2⟩,⟨.covers 526,1,2⟩,⟨.covers 3078,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 778,1,2⟩,⟨.covers 1546,1,2⟩,⟨.covers 3330,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 1188,1,1⟩,⟨.covers 2820,1,2⟩,⟨.covers 3588,1,2⟩,⟨.covers 3168,1,1⟩,⟨.covers 1824,1,1⟩,⟨.covers 2752,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_015
