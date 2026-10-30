import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source28
namespace C13.Global.FastDual28_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,9,11]
def points : Finset C13.Point := {1,3,9,11}
def columns : List Code := [247,251,253,254,381,471,499,501,502,505,506,508,701,743,755,757,758,761,762,764,829,885,892,953,956,967,979,981,995,998,1009,1010,1012,1016,1143,1245,1267,1269,1270,1273,1274,1276,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1491,1493,1494,1497,1498,1500,1509,1521,1522,1524,1528,1639,1653,1654,1693,1721,1724,1749,1753,1763,1766,1777,1778,1780,1784,1821,1852,1863,1877,1894,1908,1945,1976,1987,2001,2018,2032,2231,2285,2291,2293,2294,2297,2298,2300,2413,2421,2425,2455,2483,2486,2517,2518,2537,2540,2545,2546,2548,2552,2677,2731,2734,2746,2773,2794,2801,2802,2804,2808,2901,2986,3056,3127,3187,3189,3251,3254,3277,3285,3292,3305,3308,3313,3314,3316,3320,3351,3379,3405,3413,3433,3441,3478,3506,3532,3540,3560,3568,3669,3754,3824]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 267,1,2⟩,⟨.covers 523,1,2⟩,⟨.covers 1539,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 1185,1,1⟩,⟨.covers 270,1,2⟩,⟨.covers 526,1,2⟩,⟨.covers 3078,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 778,1,2⟩,⟨.covers 1546,1,2⟩,⟨.covers 2316,1,1⟩,⟨.covers 420,1,1⟩,⟨.covers 2820,1,2⟩,⟨.covers 3588,1,2⟩,⟨.covers 3336,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 1824,1,1⟩,⟨.covers 2752,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_008
namespace C13.Global.FastDual28_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,9,10]
def points : Finset C13.Point := {1,7,9,10}
def columns : List Code := [381,471,637,747,829,861,885,892,967,971,979,995,1143,1147,1150,1213,1245,1261,1371,1374,1395,1398,1402,1437,1453,1461,1485,1509,1639,1646,1654,1693,1721,1753,1894,1945,2173,2238,2365,2397,2413,2421,2425,2428,2455,2462,2486,2518,2621,2653,2677,2684,2731,2734,2746,2794,2845,2876,2901,2932,2955,2986,3011,3042,3127,3131,3187,3190,3194,3229,3245,3277,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 2055,1,5⟩,⟨.covers 1035,1,5⟩,⟨.covers 83,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 1539,1,16⟩,⟨.covers 2563,1,13⟩,⟨.covers 141,1,1⟩,⟨.covers 525,1,4⟩,⟨.covers 197,1,2⟩,⟨.covers 773,1,4⟩,⟨.covers 3077,1,3⟩,⟨.covers 2129,1,4⟩,⟨.covers 1313,1,1⟩,⟨.covers 3105,1,1⟩,⟨.covers 270,1,5⟩,⟨.covers 526,1,6⟩,⟨.covers 166,1,3⟩,⟨.covers 774,1,7⟩,⟨.covers 202,1,11⟩,⟨.covers 330,1,2⟩,⟨.covers 3082,1,2⟩,⟨.covers 178,1,3⟩,⟨.covers 210,1,1⟩,⟨.covers 1794,1,9⟩,⟨.covers 3586,1,16⟩,⟨.covers 300,1,4⟩,⟨.covers 1292,1,1⟩,⟨.covers 1548,1,10⟩,⟨.covers 2572,1,4⟩,⟨.covers 228,1,2⟩,⟨.covers 3332,1,1⟩,⟨.covers 232,1,2⟩,⟨.covers 3144,1,1⟩,⟨.covers 1800,1,15⟩,⟨.covers 3336,1,1⟩,⟨.covers 3592,1,15⟩,⟨.covers 624,1,4⟩,⟨.covers 688,1,6⟩,⟨.covers 1328,1,6⟩,⟨.covers 1584,1,8⟩,⟨.covers 2608,1,4⟩,⟨.covers 2256,1,4⟩,⟨.covers 848,1,4⟩,⟨.covers 1616,1,4⟩,⟨.covers 3152,1,2⟩,⟨.covers 928,1,13⟩,⟨.covers 3232,1,2⟩,⟨.covers 1472,1,3⟩,⟨.covers 1728,1,11⟩,⟨.incident 1,8,-1⟩,⟨.incident 9,8,-8⟩,⟨.incident 10,8,-3⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_009
namespace C13.Global.FastDual28_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,9,11]
def points : Finset C13.Point := {1,7,9,11}
def columns : List Code := [381,471,637,747,829,861,885,892,967,971,979,995,1143,1147,1149,1150,1213,1245,1261,1341,1367,1371,1373,1374,1389,1395,1397,1398,1401,1402,1404,1437,1453,1461,1485,1493,1509,1597,1629,1639,1646,1653,1654,1660,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2173,2238,2397,2413,2421,2425,2455,2462,2486,2518,2653,2677,2731,2734,2746,2794,2901,2986,3127,3131,3165,3181,3187,3189,3193,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 267,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 1539,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 624,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 2608,1,1⟩,⟨.covers 912,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 3456,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_010
namespace C13.Global.FastDual28_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,10,11]
def points : Finset C13.Point := {1,7,10,11}
def columns : List Code := [381,471,637,747,829,861,877,885,889,892,967,971,979,995,1143,1147,1150,1213,1245,1261,1371,1374,1395,1398,1402,1437,1453,1461,1485,1509,1639,1646,1651,1654,1658,1693,1709,1721,1741,1753,1870,1882,1894,1906,1933,1945,1957,1969,2173,2238,2397,2413,2421,2425,2455,2462,2486,2518,2653,2669,2677,2681,2731,2734,2746,2794,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3187,3277,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 519,1,5⟩,⟨.covers 267,1,6⟩,⟨.covers 2059,1,8⟩,⟨.covers 2307,1,4⟩,⟨.covers 141,1,3⟩,⟨.covers 2061,1,4⟩,⟨.covers 149,1,2⟩,⟨.covers 533,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,2⟩,⟨.covers 3077,1,1⟩,⟨.covers 297,1,3⟩,⟨.covers 1289,1,2⟩,⟨.covers 2569,1,4⟩,⟨.covers 3081,1,7⟩,⟨.covers 78,1,6⟩,⟨.covers 86,1,2⟩,⟨.covers 166,1,8⟩,⟨.covers 550,1,2⟩,⟨.covers 2566,1,1⟩,⟨.covers 3078,1,14⟩,⟨.covers 282,1,1⟩,⟨.covers 2314,1,10⟩,⟨.covers 1546,1,2⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,6⟩,⟨.covers 3330,1,10⟩,⟨.covers 3586,1,15⟩,⟨.covers 180,1,2⟩,⟨.covers 564,1,1⟩,⟨.covers 596,1,3⟩,⟨.covers 420,1,1⟩,⟨.covers 804,1,1⟩,⟨.covers 3332,1,15⟩,⟨.covers 3588,1,15⟩,⟨.covers 120,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 792,1,1⟩,⟨.covers 1560,1,2⟩,⟨.covers 1800,1,2⟩,⟨.covers 2160,1,3⟩,⟨.covers 1200,1,2⟩,⟨.covers 720,1,5⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,2⟩,⟨.covers 1424,1,3⟩,⟨.covers 2704,1,10⟩,⟨.covers 3216,1,15⟩,⟨.covers 2272,1,2⟩,⟨.covers 1376,1,7⟩,⟨.covers 2656,1,3⟩,⟨.covers 1696,1,5⟩,⟨.covers 3232,1,12⟩,⟨.covers 2848,1,1⟩,⟨.covers 1920,1,1⟩,⟨.incident 10,8,-4⟩,⟨.incident 11,8,-5⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_011
namespace C13.Global.FastDual28_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,9]
def points : Finset C13.Point := {2,3,7,9}
def columns : List Code := [379,439,631,699,829,830,885,886,892,979,995,1371,1395,1401,1402,1447,1461,1509,1639,1653,1654,1691,1721,1753,1852,1894,1908,1945,1987,2001,2411,2419,2425,2426,2455,2486,2518,2647,2677,2678,2731,2746,2794,2876,2901,2932,2986,3011,3042,3187,3277,3278,3292,3308,3379,3403,3411,3417,3418,3427,3433,3434,3441,3442,3448,3463,3477,3478,3493,3494,3508,3525,3526,3532,3540,3556,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 77,1,18⟩,⟨.covers 269,1,18⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,4⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,1⟩,⟨.covers 89,1,5⟩,⟨.covers 169,1,10⟩,⟨.covers 2089,1,2⟩,⟨.covers 1289,1,5⟩,⟨.covers 2569,1,2⟩,⟨.covers 2577,1,1⟩,⟨.covers 2145,1,1⟩,⟨.covers 1185,1,1⟩,⟨.covers 2337,1,1⟩,⟨.covers 78,1,18⟩,⟨.covers 270,1,18⟩,⟨.covers 86,1,2⟩,⟨.covers 166,1,2⟩,⟨.covers 1286,1,2⟩,⟨.covers 2566,1,2⟩,⟨.covers 1050,1,2⟩,⟨.covers 106,1,5⟩,⟨.covers 2314,1,5⟩,⟨.covers 1546,1,12⟩,⟨.covers 210,1,2⟩,⟨.covers 1106,1,1⟩,⟨.covers 2194,1,1⟩,⟨.covers 1298,1,1⟩,⟨.covers 1570,1,1⟩,⟨.covers 1794,1,2⟩,⟨.covers 2818,1,2⟩,⟨.covers 92,1,10⟩,⟨.covers 108,1,4⟩,⟨.covers 172,1,4⟩,⟨.covers 2316,1,10⟩,⟨.covers 1548,1,10⟩,⟨.covers 180,1,2⟩,⟨.covers 228,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3588,1,2⟩,⟨.covers 120,1,5⟩,⟨.covers 184,1,2⟩,⟨.covers 216,1,8⟩,⟨.covers 232,1,10⟩,⟨.covers 1800,1,8⟩,⟨.covers 2824,1,7⟩,⟨.covers 3336,1,5⟩,⟨.covers 1616,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 2704,1,11⟩,⟨.covers 1696,1,1⟩,⟨.incident 2,8,-4⟩,⟨.incident 3,8,-12⟩]
def bound : Int := 3

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_012
namespace C13.Global.FastDual28_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,10]
def points : Finset C13.Point := {2,3,7,10}
def columns : List Code := [379,439,631,699,823,827,829,830,883,885,886,889,890,892,947,979,995,1371,1395,1402,1447,1461,1509,1639,1651,1654,1691,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2411,2419,2425,2426,2455,2486,2518,2647,2675,2677,2678,2731,2746,2794,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2902,2915,2921,2922,2929,2930,2932,2936,2963,2966,2979,2986,2994,3011,3026,3042,3187,3277,3278,3292,3308,3379,3418,3442,3493,3532,3556,3635,3686,3698,3737,3788,3800,3854,3866,3878,3890,3980,3992,4004,4016]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 269,1,2⟩,⟨.covers 2309,1,1⟩,⟨.covers 1541,1,2⟩,⟨.covers 1289,1,2⟩,⟨.covers 2569,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 3105,1,1⟩,⟨.covers 78,1,2⟩,⟨.covers 270,1,2⟩,⟨.covers 166,1,2⟩,⟨.covers 154,1,2⟩,⟨.covers 210,1,2⟩,⟨.covers 226,1,2⟩,⟨.covers 3106,1,1⟩,⟨.covers 156,1,2⟩,⟨.covers 172,1,2⟩,⟨.covers 116,1,1⟩,⟨.covers 2628,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 2376,1,1⟩,⟨.covers 1200,1,2⟩,⟨.covers 1616,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_013
namespace C13.Global.FastDual28_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,11]
def points : Finset C13.Point := {2,3,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,883,885,886,889,890,892,947,979,995,1371,1395,1401,1402,1447,1461,1509,1639,1651,1653,1654,1691,1721,1753,1819,1831,1843,1845,1846,1849,1850,1852,1875,1881,1882,1891,1893,1894,1905,1906,1908,1912,1939,1945,1955,1957,1969,1987,2001,2017,2411,2419,2425,2455,2486,2518,2647,2675,2677,2731,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3187,3277,3278,3292,3308,3379,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 75,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 166,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 2704,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_014
namespace C13.Global.FastDual28_015
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,10,11]
def points : Finset C13.Point := {2,3,10,11}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,823,827,829,830,883,885,886,889,890,892,947,949,950,953,954,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1395,1402,1447,1459,1461,1497,1498,1509,1510,1521,1522,1524,1528,1639,1651,1654,1691,1715,1721,1753,1754,1765,1766,1777,1778,1780,1784,1819,1831,1843,1882,1894,1906,1945,1957,1969,2008,2020,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2419,2425,2455,2483,2486,2517,2518,2537,2538,2545,2546,2548,2552,2647,2675,2677,2731,2739,2746,2773,2774,2793,2794,2801,2802,2804,2808,2839,2859,2867,2901,2921,2929,2966,2986,2994,3028,3048,3056,3187,3251,3277,3278,3292,3308,3313,3314,3316,3320,3379,3532,3568,3635,3788,3824]
def rows : List LinearRow := [⟨.covers 71,1,5⟩,⟨.covers 135,1,4⟩,⟨.covers 1031,1,4⟩,⟨.covers 2055,1,2⟩,⟨.covers 75,1,4⟩,⟨.covers 139,1,4⟩,⟨.covers 1035,1,1⟩,⟨.covers 2059,1,5⟩,⟨.covers 269,1,19⟩,⟨.covers 1037,1,19⟩,⟨.covers 101,1,1⟩,⟨.covers 2309,1,11⟩,⟨.covers 1541,1,2⟩,⟨.covers 89,1,5⟩,⟨.covers 169,1,1⟩,⟨.covers 1289,1,5⟩,⟨.covers 2569,1,7⟩,⟨.covers 2129,1,1⟩,⟨.covers 1169,1,1⟩,⟨.covers 2145,1,3⟩,⟨.covers 1185,1,3⟩,⟨.covers 705,1,8⟩,⟨.covers 270,1,19⟩,⟨.covers 1038,1,19⟩,⟨.covers 86,1,4⟩,⟨.covers 1286,1,8⟩,⟨.covers 2566,1,4⟩,⟨.covers 2314,1,3⟩,⟨.covers 1546,1,12⟩,⟨.covers 178,1,4⟩,⟨.covers 2194,1,1⟩,⟨.covers 1122,1,1⟩,⟨.covers 2210,1,2⟩,⟨.covers 450,1,8⟩,⟨.covers 706,1,2⟩,⟨.covers 3330,1,19⟩,⟨.covers 3586,1,19⟩,⟨.covers 92,1,4⟩,⟨.covers 156,1,6⟩,⟨.covers 1292,1,19⟩,⟨.covers 1548,1,19⟩,⟨.covers 2132,1,2⟩,⟨.covers 404,1,1⟩,⟨.covers 612,1,4⟩,⟨.covers 420,1,1⟩,⟨.covers 1796,1,5⟩,⟨.covers 2820,1,2⟩,⟨.covers 344,1,2⟩,⟨.covers 1112,1,3⟩,⟨.covers 360,1,5⟩,⟨.covers 1800,1,1⟩,⟨.covers 2824,1,5⟩,⟨.covers 624,1,4⟩,⟨.covers 2384,1,3⟩,⟨.covers 1616,1,2⟩,⟨.covers 1424,1,4⟩,⟨.covers 2704,1,3⟩,⟨.covers 1376,1,1⟩,⟨.covers 3168,1,11⟩,⟨.covers 2464,1,1⟩,⟨.covers 1920,1,9⟩,⟨.covers 2944,1,8⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_015
