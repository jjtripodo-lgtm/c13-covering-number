import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source38
namespace C13.Global.FastDual38_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,9,10]
def points : Finset C13.Point := {1,7,9,10}
def columns : List Code := [381,471,637,747,829,861,885,892,967,971,979,995,1143,1147,1150,1213,1245,1261,1371,1374,1395,1398,1402,1437,1453,1461,1485,1509,1639,1646,1654,1693,1721,1753,1894,1945,2173,2238,2365,2397,2413,2421,2425,2428,2455,2462,2486,2518,2621,2653,2677,2684,2731,2734,2746,2794,2845,2876,2901,2932,2955,2986,3011,3042,3127,3131,3187,3190,3194,3229,3245,3277,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 519,1,7⟩,⟨.covers 2055,1,5⟩,⟨.covers 1035,1,5⟩,⟨.covers 83,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 1539,1,9⟩,⟨.covers 2563,1,13⟩,⟨.covers 141,1,1⟩,⟨.covers 525,1,4⟩,⟨.covers 197,1,2⟩,⟨.covers 773,1,4⟩,⟨.covers 3077,1,3⟩,⟨.covers 2129,1,4⟩,⟨.covers 1313,1,1⟩,⟨.covers 3105,1,1⟩,⟨.covers 1793,1,15⟩,⟨.covers 3585,1,15⟩,⟨.covers 270,1,5⟩,⟨.covers 526,1,4⟩,⟨.covers 166,1,5⟩,⟨.covers 202,1,13⟩,⟨.covers 1546,1,3⟩,⟨.covers 3082,1,2⟩,⟨.covers 210,1,1⟩,⟨.covers 1794,1,16⟩,⟨.covers 3586,1,16⟩,⟨.covers 300,1,4⟩,⟨.covers 1292,1,1⟩,⟨.covers 1548,1,10⟩,⟨.covers 2572,1,4⟩,⟨.covers 228,1,4⟩,⟨.covers 3332,1,1⟩,⟨.covers 1352,1,2⟩,⟨.covers 3144,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 624,1,4⟩,⟨.covers 688,1,9⟩,⟨.covers 1328,1,6⟩,⟨.covers 2608,1,4⟩,⟨.covers 720,1,3⟩,⟨.covers 2256,1,4⟩,⟨.covers 848,1,4⟩,⟨.covers 1616,1,12⟩,⟨.covers 3152,1,2⟩,⟨.covers 928,1,13⟩,⟨.covers 1696,1,6⟩,⟨.covers 3232,1,2⟩,⟨.covers 1472,1,1⟩,⟨.incident 1,8,-1⟩,⟨.incident 9,8,-8⟩,⟨.incident 10,8,-3⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source38.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source38.rootCodes link38 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual38_008
namespace C13.Global.FastDual38_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,9,11]
def points : Finset C13.Point := {1,7,9,11}
def columns : List Code := [381,471,637,747,829,861,885,892,967,971,979,995,1143,1147,1149,1150,1213,1245,1261,1341,1367,1371,1373,1374,1389,1395,1397,1398,1401,1402,1404,1437,1453,1461,1485,1493,1509,1597,1629,1639,1646,1653,1654,1660,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2173,2238,2397,2413,2421,2425,2455,2462,2486,2518,2653,2677,2731,2734,2746,2794,2901,2986,3127,3131,3165,3181,3187,3189,3193,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 267,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 1539,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 2337,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 804,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 624,1,1⟩,⟨.covers 688,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 2608,1,1⟩,⟨.covers 912,1,1⟩,⟨.covers 928,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 1920,1,1⟩,⟨.covers 3456,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source38.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source38.rootCodes link38 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual38_009
namespace C13.Global.FastDual38_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,10,11]
def points : Finset C13.Point := {1,7,10,11}
def columns : List Code := [381,471,637,747,829,861,877,885,889,892,967,971,979,995,1143,1147,1150,1213,1245,1261,1371,1374,1395,1398,1402,1437,1453,1461,1485,1509,1639,1646,1651,1654,1658,1693,1709,1721,1741,1753,1870,1882,1894,1906,1933,1945,1957,1969,2173,2238,2397,2413,2421,2425,2455,2462,2486,2518,2653,2669,2677,2681,2731,2734,2746,2794,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3187,3277,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 267,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 1289,1,1⟩,⟨.covers 3329,1,2⟩,⟨.covers 3585,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 3082,1,2⟩,⟨.covers 114,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 3332,1,1⟩,⟨.covers 3588,1,2⟩,⟨.covers 1200,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 3216,1,2⟩,⟨.covers 2464,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 2496,1,1⟩,⟨.incident 10,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source38.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source38.rootCodes link38 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual38_010
namespace C13.Global.FastDual38_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,9]
def points : Finset C13.Point := {2,3,7,9}
def columns : List Code := [379,439,631,699,829,830,885,886,892,979,995,1371,1395,1401,1402,1447,1461,1509,1639,1653,1654,1691,1721,1753,1852,1894,1908,1945,1987,2001,2411,2419,2425,2426,2455,2486,2518,2647,2677,2678,2731,2746,2794,2876,2901,2932,2986,3011,3042,3187,3277,3278,3292,3308,3379,3403,3411,3417,3418,3427,3433,3434,3441,3442,3448,3463,3477,3478,3493,3494,3508,3525,3526,3532,3540,3556,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 2055,1,2⟩,⟨.covers 2067,1,2⟩,⟨.covers 77,1,15⟩,⟨.covers 269,1,15⟩,⟨.covers 149,1,2⟩,⟨.covers 101,1,6⟩,⟨.covers 2309,1,2⟩,⟨.covers 89,1,4⟩,⟨.covers 169,1,2⟩,⟨.covers 1289,1,4⟩,⟨.covers 2569,1,10⟩,⟨.covers 2145,1,2⟩,⟨.covers 1185,1,2⟩,⟨.covers 2337,1,2⟩,⟨.covers 1793,1,2⟩,⟨.covers 2817,1,6⟩,⟨.covers 78,1,12⟩,⟨.covers 270,1,6⟩,⟨.covers 86,1,2⟩,⟨.covers 166,1,4⟩,⟨.covers 1286,1,2⟩,⟨.covers 2566,1,2⟩,⟨.covers 154,1,10⟩,⟨.covers 106,1,4⟩,⟨.covers 202,1,2⟩,⟨.covers 778,1,8⟩,⟨.covers 2314,1,4⟩,⟨.covers 1546,1,2⟩,⟨.covers 210,1,6⟩,⟨.covers 1106,1,2⟩,⟨.covers 1298,1,2⟩,⟨.covers 226,1,6⟩,⟨.covers 1570,1,2⟩,⟨.covers 1794,1,4⟩,⟨.covers 156,1,8⟩,⟨.covers 108,1,10⟩,⟨.covers 172,1,4⟩,⟨.covers 2316,1,8⟩,⟨.covers 1548,1,10⟩,⟨.covers 2572,1,6⟩,⟨.covers 180,1,2⟩,⟨.covers 3332,1,2⟩,⟨.covers 3588,1,4⟩,⟨.covers 120,1,4⟩,⟨.covers 216,1,6⟩,⟨.covers 1800,1,4⟩,⟨.covers 3336,1,4⟩,⟨.covers 2224,1,2⟩,⟨.covers 1616,1,2⟩,⟨.covers 1424,1,2⟩,⟨.covers 3600,1,2⟩,⟨.covers 1696,1,8⟩,⟨.incident 2,8,-2⟩,⟨.incident 3,8,-6⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source38.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source38.rootCodes link38 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual38_011
namespace C13.Global.FastDual38_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,10]
def points : Finset C13.Point := {2,3,7,10}
def columns : List Code := [379,439,631,699,823,827,829,830,883,885,886,889,890,892,947,979,995,1371,1395,1402,1447,1461,1509,1639,1651,1654,1691,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2411,2419,2425,2426,2455,2486,2518,2647,2675,2677,2678,2731,2746,2794,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2902,2915,2921,2922,2929,2930,2932,2936,2963,2966,2979,2986,2994,3011,3026,3042,3187,3277,3278,3292,3308,3379,3418,3442,3493,3532,3556,3635,3686,3698,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 2224,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 1424,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source38.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source38.rootCodes link38 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual38_012
namespace C13.Global.FastDual38_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,11]
def points : Finset C13.Point := {2,3,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,883,885,886,889,890,892,947,979,995,1371,1395,1401,1402,1447,1461,1509,1639,1651,1653,1654,1691,1721,1753,1819,1831,1843,1845,1846,1849,1850,1852,1875,1881,1882,1891,1893,1894,1905,1906,1908,1912,1939,1945,1955,1957,1969,1987,2001,2017,2411,2419,2425,2455,2486,2518,2647,2675,2677,2731,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3187,3277,3278,3292,3308,3379,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 166,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 1248,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source38.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source38.rootCodes link38 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual38_013
namespace C13.Global.FastDual38_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,10,11]
def points : Finset C13.Point := {2,3,10,11}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,823,827,829,830,883,885,886,889,890,892,947,949,950,953,954,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1395,1402,1447,1459,1461,1497,1498,1509,1510,1521,1522,1524,1528,1639,1651,1654,1691,1715,1721,1753,1754,1765,1766,1777,1778,1780,1784,1819,1831,1843,1882,1894,1906,1945,1957,1969,2008,2020,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2419,2425,2455,2483,2486,2517,2518,2537,2538,2545,2546,2548,2552,2647,2675,2677,2731,2739,2746,2773,2774,2793,2794,2801,2802,2804,2808,2839,2859,2867,2901,2921,2929,2966,2986,2994,3028,3048,3056,3187,3251,3277,3278,3292,3308,3313,3314,3316,3320,3379,3532,3568,3635,3788,3824]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 269,1,2⟩,⟨.covers 1037,1,2⟩,⟨.covers 2309,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 705,1,1⟩,⟨.covers 3329,1,2⟩,⟨.covers 3585,1,2⟩,⟨.covers 270,1,2⟩,⟨.covers 1038,1,2⟩,⟨.covers 1286,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 450,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 1292,1,2⟩,⟨.covers 1548,1,2⟩,⟨.covers 1796,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 1920,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source38.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source38.rootCodes link38 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual38_014
namespace C13.Global.FastDual38_015
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,10]
def points : Finset C13.Point := {2,7,9,10}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1639,1646,1654,1691,1721,1753,1894,1945,2171,2270,2363,2395,2411,2419,2425,2426,2455,2462,2486,2518,2647,2653,2677,2678,2684,2715,2731,2746,2763,2794,2845,2876,2901,2932,2955,2986,3011,3042,3131,3163,3187,3194,3277,3278,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 2055,1,6⟩,⟨.covers 139,1,2⟩,⟨.covers 1035,1,4⟩,⟨.covers 163,1,1⟩,⟨.covers 1283,1,4⟩,⟨.covers 1539,1,2⟩,⟨.covers 2563,1,2⟩,⟨.covers 525,1,5⟩,⟨.covers 197,1,14⟩,⟨.covers 773,1,2⟩,⟨.covers 1541,1,15⟩,⟨.covers 2097,1,4⟩,⟨.covers 833,1,1⟩,⟨.covers 2625,1,2⟩,⟨.covers 1793,1,3⟩,⟨.covers 3585,1,13⟩,⟨.covers 270,1,7⟩,⟨.covers 1038,1,11⟩,⟨.covers 166,1,5⟩,⟨.covers 1286,1,4⟩,⟨.covers 330,1,4⟩,⟨.covers 1546,1,6⟩,⟨.covers 3082,1,4⟩,⟨.covers 226,1,4⟩,⟨.covers 1794,1,13⟩,⟨.covers 2818,1,1⟩,⟨.covers 3586,1,17⟩,⟨.covers 1292,1,14⟩,⟨.covers 2572,1,3⟩,⟨.covers 116,1,2⟩,⟨.covers 212,1,7⟩,⟨.covers 808,1,3⟩,⟨.covers 2600,1,2⟩,⟨.covers 1136,1,4⟩,⟨.covers 2224,1,2⟩,⟨.covers 1328,1,4⟩,⟨.covers 2608,1,3⟩,⟨.covers 1232,1,2⟩,⟨.covers 848,1,5⟩,⟨.covers 1616,1,11⟩,⟨.covers 3152,1,4⟩,⟨.covers 1424,1,11⟩,⟨.covers 928,1,1⟩,⟨.covers 1696,1,13⟩,⟨.covers 3232,1,14⟩,⟨.covers 2752,1,1⟩,⟨.incident 2,8,-4⟩,⟨.incident 9,8,-3⟩,⟨.incident 10,8,-7⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source38.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source38.rootCodes link38 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual38_015
