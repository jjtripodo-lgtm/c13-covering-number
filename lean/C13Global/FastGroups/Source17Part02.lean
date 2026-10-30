import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source17
namespace C13.Global.FastDual17_016
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,8,11]
def points : Finset C13.Point := {1,7,8,11}
def columns : List Code := [381,471,637,747,829,877,889,892,967,971,979,995,1143,1147,1149,1150,1213,1245,1261,1341,1371,1374,1389,1401,1402,1404,1453,1461,1509,1597,1629,1639,1643,1645,1646,1651,1653,1654,1657,1658,1660,1693,1709,1721,1741,1753,1769,1837,1852,1867,1882,1897,1912,1957,1987,2017,2173,2238,2413,2425,2455,2462,2486,2518,2653,2669,2677,2681,2731,2734,2746,2794,2921,2966,3127,3131,3165,3181,3187,3189,3193,3277,3292,3308,3433,3478,3627,3635,3661,3669,3689,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 519,1,6⟩,⟨.covers 1031,1,6⟩,⟨.covers 139,1,5⟩,⟨.covers 267,1,3⟩,⟨.covers 83,1,2⟩,⟨.covers 1043,1,3⟩,⟨.covers 2307,1,6⟩,⟨.covers 2563,1,6⟩,⟨.covers 141,1,5⟩,⟨.covers 269,1,2⟩,⟨.covers 2061,1,4⟩,⟨.covers 533,1,2⟩,⟨.covers 773,1,6⟩,⟨.covers 2309,1,6⟩,⟨.covers 3077,1,2⟩,⟨.covers 78,1,4⟩,⟨.covers 526,1,7⟩,⟨.covers 1286,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 1050,1,3⟩,⟨.covers 202,1,3⟩,⟨.covers 2314,1,11⟩,⟨.covers 3082,1,5⟩,⟨.covers 114,1,1⟩,⟨.covers 226,1,3⟩,⟨.covers 1794,1,8⟩,⟨.covers 2818,1,11⟩,⟨.covers 3330,1,7⟩,⟨.covers 92,1,4⟩,⟨.covers 540,1,2⟩,⟨.covers 172,1,4⟩,⟨.covers 1188,1,1⟩,⟨.covers 1220,1,1⟩,⟨.covers 1796,1,4⟩,⟨.covers 3588,1,6⟩,⟨.covers 216,1,2⟩,⟨.covers 2824,1,11⟩,⟨.covers 3336,1,11⟩,⟨.covers 368,1,2⟩,⟨.covers 624,1,4⟩,⟨.covers 2160,1,4⟩,⟨.covers 688,1,9⟩,⟨.covers 1200,1,2⟩,⟨.covers 1328,1,6⟩,⟨.covers 2352,1,6⟩,⟨.covers 2608,1,2⟩,⟨.covers 720,1,9⟩,⟨.covers 3152,1,2⟩,⟨.covers 1424,1,3⟩,⟨.covers 480,1,8⟩,⟨.covers 2272,1,5⟩,⟨.covers 2464,1,6⟩,⟨.covers 3232,1,1⟩,⟨.covers 1472,1,2⟩,⟨.covers 2496,1,11⟩,⟨.covers 1920,1,1⟩,⟨.covers 3712,1,5⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_016
namespace C13.Global.FastDual17_017
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,9,10]
def points : Finset C13.Point := {1,7,9,10}
def columns : List Code := [381,471,637,747,829,861,885,892,967,971,979,995,1143,1147,1150,1213,1245,1261,1371,1374,1395,1398,1402,1437,1453,1461,1485,1509,1639,1646,1654,1693,1721,1753,1894,1945,2173,2238,2365,2397,2413,2421,2425,2428,2455,2462,2486,2518,2621,2653,2677,2684,2731,2734,2746,2794,2845,2876,2901,2932,2955,2986,3011,3042,3127,3131,3187,3190,3194,3229,3245,3277,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 83,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 1541,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 432,1,1⟩,⟨.covers 1328,1,1⟩,⟨.covers 2256,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 1248,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 2752,1,1⟩,⟨.incident 10,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_017
namespace C13.Global.FastDual17_018
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,9,11]
def points : Finset C13.Point := {1,7,9,11}
def columns : List Code := [381,471,637,747,829,861,885,892,967,971,979,995,1143,1147,1149,1150,1213,1245,1261,1341,1367,1371,1373,1374,1389,1395,1397,1398,1401,1402,1404,1437,1453,1461,1485,1493,1509,1597,1629,1639,1646,1653,1654,1660,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2173,2238,2397,2413,2421,2425,2455,2462,2486,2518,2653,2677,2731,2734,2746,2794,2901,2986,3127,3131,3165,3181,3187,3189,3193,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 519,1,1⟩,⟨.covers 267,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 2608,1,1⟩,⟨.covers 1248,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_018
namespace C13.Global.FastDual17_019
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,10,11]
def points : Finset C13.Point := {1,7,10,11}
def columns : List Code := [381,471,637,747,829,861,877,885,889,892,967,971,979,995,1143,1147,1150,1213,1245,1261,1371,1374,1395,1398,1402,1437,1453,1461,1485,1509,1639,1646,1651,1654,1658,1693,1709,1721,1741,1753,1870,1882,1894,1906,1933,1945,1957,1969,2173,2238,2397,2413,2421,2425,2455,2462,2486,2518,2653,2669,2677,2681,2731,2734,2746,2794,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3187,3277,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 519,1,7⟩,⟨.covers 267,1,8⟩,⟨.covers 2059,1,1⟩,⟨.covers 147,1,2⟩,⟨.covers 2307,1,2⟩,⟨.covers 77,1,2⟩,⟨.covers 141,1,2⟩,⟨.covers 533,1,2⟩,⟨.covers 2309,1,5⟩,⟨.covers 1541,1,4⟩,⟨.covers 169,1,5⟩,⟨.covers 1289,1,4⟩,⟨.covers 2569,1,2⟩,⟨.covers 3081,1,10⟩,⟨.covers 78,1,6⟩,⟨.covers 86,1,6⟩,⟨.covers 166,1,8⟩,⟨.covers 3078,1,13⟩,⟨.covers 106,1,1⟩,⟨.covers 2314,1,8⟩,⟨.covers 1546,1,4⟩,⟨.covers 3082,1,3⟩,⟨.covers 114,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 3330,1,12⟩,⟨.covers 3586,1,13⟩,⟨.covers 540,1,3⟩,⟨.covers 1316,1,2⟩,⟨.covers 1572,1,2⟩,⟨.covers 1796,1,3⟩,⟨.covers 3332,1,13⟩,⟨.covers 3588,1,13⟩,⟨.covers 312,1,3⟩,⟨.covers 1304,1,1⟩,⟨.covers 1560,1,2⟩,⟨.covers 360,1,2⟩,⟨.covers 2160,1,2⟩,⟨.covers 1200,1,6⟩,⟨.covers 720,1,6⟩,⟨.covers 2384,1,2⟩,⟨.covers 1616,1,6⟩,⟨.covers 1424,1,6⟩,⟨.covers 2704,1,8⟩,⟨.covers 3216,1,13⟩,⟨.covers 480,1,6⟩,⟨.covers 1376,1,6⟩,⟨.covers 2656,1,5⟩,⟨.covers 3168,1,11⟩,⟨.covers 3232,1,2⟩,⟨.covers 1824,1,2⟩,⟨.covers 2752,1,1⟩,⟨.incident 10,8,-6⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_019
namespace C13.Global.FastDual17_020
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,8,9]
def points : Finset C13.Point := {3,7,8,9}
def columns : List Code := [379,381,382,439,471,487,631,699,829,830,892,967,979,995,1143,1245,1371,1374,1401,1402,1404,1431,1447,1461,1479,1509,1623,1639,1653,1654,1691,1693,1721,1753,1852,1987,2167,2286,2411,2413,2425,2426,2428,2455,2471,2486,2503,2518,2647,2663,2677,2678,2731,2734,2746,2794,2876,3011,3127,3159,3175,3187,3189,3190,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 75,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 1038,1,1⟩,⟨.covers 166,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 432,1,1⟩,⟨.covers 2256,1,1⟩,⟨.covers 2384,1,1⟩,⟨.covers 912,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 1248,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 928,1,1⟩,⟨.covers 1696,1,1⟩,⟨.incident 8,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_020
namespace C13.Global.FastDual17_021
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,8,11]
def points : Finset C13.Point := {3,7,8,11}
def columns : List Code := [379,381,382,439,471,487,631,699,829,830,889,890,892,919,935,967,979,995,1143,1245,1371,1374,1401,1402,1404,1431,1447,1461,1479,1509,1591,1623,1639,1651,1653,1654,1691,1693,1721,1753,1822,1852,1882,1912,1927,1957,1987,2017,2167,2286,2411,2413,2425,2455,2486,2518,2615,2647,2675,2677,2731,2734,2746,2794,2921,2966,3127,3159,3187,3189,3277,3278,3292,3308,3433,3478,3607,3635,3669,3697,3726,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 135,1,2⟩,⟨.covers 2055,1,2⟩,⟨.covers 1035,1,8⟩,⟨.covers 163,1,5⟩,⟨.covers 1283,1,4⟩,⟨.covers 2307,1,10⟩,⟨.covers 2563,1,2⟩,⟨.covers 141,1,2⟩,⟨.covers 525,1,5⟩,⟨.covers 581,1,2⟩,⟨.covers 773,1,5⟩,⟨.covers 3077,1,5⟩,⟨.covers 2569,1,1⟩,⟨.covers 78,1,2⟩,⟨.covers 270,1,5⟩,⟨.covers 582,1,3⟩,⟨.covers 202,1,5⟩,⟨.covers 778,1,6⟩,⟨.covers 2314,1,3⟩,⟨.covers 3082,1,2⟩,⟨.covers 1074,1,2⟩,⟨.covers 226,1,2⟩,⟨.covers 1122,1,3⟩,⟨.covers 834,1,2⟩,⟨.covers 1346,1,2⟩,⟨.covers 2818,1,12⟩,⟨.covers 3330,1,12⟩,⟨.covers 92,1,5⟩,⟨.covers 556,1,2⟩,⟨.covers 2316,1,13⟩,⟨.covers 2572,1,6⟩,⟨.covers 1188,1,2⟩,⟨.covers 804,1,1⟩,⟨.covers 1316,1,1⟩,⟨.covers 1796,1,2⟩,⟨.covers 120,1,2⟩,⟨.covers 184,1,2⟩,⟨.covers 2824,1,12⟩,⟨.covers 3336,1,13⟩,⟨.covers 2160,1,2⟩,⟨.covers 1200,1,5⟩,⟨.covers 1328,1,5⟩,⟨.covers 2352,1,10⟩,⟨.covers 2608,1,5⟩,⟨.covers 720,1,8⟩,⟨.covers 848,1,4⟩,⟨.covers 3152,1,2⟩,⟨.covers 2704,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 480,1,5⟩,⟨.covers 2464,1,3⟩,⟨.covers 3232,1,6⟩,⟨.covers 1824,1,2⟩,⟨.covers 1472,1,6⟩,⟨.covers 2496,1,13⟩,⟨.covers 2752,1,2⟩,⟨.incident 8,8,-5⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_021
namespace C13.Global.FastDual17_022
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,10]
def points : Finset C13.Point := {3,7,9,10}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1371,1374,1383,1395,1398,1402,1447,1461,1509,1639,1654,1691,1693,1721,1753,1894,1945,2167,2286,2359,2391,2407,2411,2413,2414,2419,2421,2422,2425,2426,2428,2455,2471,2486,2503,2518,2534,2647,2663,2677,2678,2731,2734,2746,2794,2862,2876,2887,2901,2918,2932,2986,3011,3042,3127,3175,3187,3190,3277,3278,3292,3308,3367,3379,3406,3418,3430,3442,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 135,1,2⟩,⟨.covers 519,1,2⟩,⟨.covers 1031,1,3⟩,⟨.covers 75,1,5⟩,⟨.covers 2059,1,5⟩,⟨.covers 83,1,1⟩,⟨.covers 2067,1,2⟩,⟨.covers 163,1,3⟩,⟨.covers 1283,1,3⟩,⟨.covers 1539,1,8⟩,⟨.covers 2563,1,4⟩,⟨.covers 269,1,5⟩,⟨.covers 2061,1,6⟩,⟨.covers 773,1,6⟩,⟨.covers 3077,1,6⟩,⟨.covers 2129,1,2⟩,⟨.covers 417,1,1⟩,⟨.covers 449,1,2⟩,⟨.covers 526,1,6⟩,⟨.covers 1038,1,6⟩,⟨.covers 282,1,2⟩,⟨.covers 778,1,3⟩,⟨.covers 1546,1,4⟩,⟨.covers 3082,1,5⟩,⟨.covers 210,1,5⟩,⟨.covers 1794,1,12⟩,⟨.covers 3586,1,12⟩,⟨.covers 92,1,3⟩,⟨.covers 284,1,1⟩,⟨.covers 172,1,5⟩,⟨.covers 1548,1,12⟩,⟨.covers 120,1,2⟩,⟨.covers 232,1,5⟩,⟨.covers 1800,1,12⟩,⟨.covers 2824,1,3⟩,⟨.covers 3592,1,12⟩,⟨.covers 624,1,3⟩,⟨.covers 1136,1,2⟩,⟨.covers 432,1,5⟩,⟨.covers 2224,1,6⟩,⟨.covers 1328,1,6⟩,⟨.covers 1584,1,8⟩,⟨.covers 2608,1,6⟩,⟨.covers 2256,1,5⟩,⟨.covers 848,1,3⟩,⟨.covers 3152,1,4⟩,⟨.covers 928,1,6⟩,⟨.covers 1696,1,4⟩,⟨.covers 1472,1,7⟩,⟨.covers 1728,1,12⟩,⟨.covers 2752,1,5⟩,⟨.covers 3456,1,5⟩,⟨.incident 9,8,-1⟩,⟨.incident 10,8,-1⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_022
namespace C13.Global.FastDual17_023
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,11]
def points : Finset C13.Point := {3,7,9,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1367,1371,1373,1374,1383,1395,1397,1398,1401,1402,1404,1431,1447,1461,1479,1493,1509,1623,1639,1653,1654,1691,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2647,2677,2731,2734,2746,2794,2901,2986,3127,3159,3187,3189,3277,3278,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 1038,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 432,1,1⟩,⟨.covers 1584,1,1⟩,⟨.covers 2608,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 480,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_023
