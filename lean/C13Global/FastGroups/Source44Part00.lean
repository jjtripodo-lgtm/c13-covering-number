import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source44
namespace C13.Global.FastDual44_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,8]
def points : Finset C13.Point := {2,3,7,8}
def columns : List Code := [379,439,631,699,829,830,889,890,892,979,995,1371,1401,1402,1447,1461,1509,1639,1651,1653,1654,1691,1721,1753,1852,1882,1912,1957,1987,2017,2411,2425,2426,2455,2486,2518,2647,2675,2677,2678,2731,2746,2794,2876,2921,2936,2966,3011,3026,3187,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3635,3655,3667,3669,3670,3683,3685,3686,3697,3698,3700,3723,3737,3738,3753,3754,3768,3785,3786,3788,3800,3816]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 2083,1,2⟩,⟨.covers 77,1,15⟩,⟨.covers 269,1,15⟩,⟨.covers 149,1,2⟩,⟨.covers 2069,1,1⟩,⟨.covers 101,1,4⟩,⟨.covers 2309,1,10⟩,⟨.covers 1541,1,4⟩,⟨.covers 89,1,5⟩,⟨.covers 1049,1,2⟩,⟨.covers 169,1,3⟩,⟨.covers 2089,1,1⟩,⟨.covers 2569,1,2⟩,⟨.covers 2577,1,3⟩,⟨.covers 1793,1,4⟩,⟨.covers 2817,1,5⟩,⟨.covers 3329,1,1⟩,⟨.covers 78,1,15⟩,⟨.covers 270,1,15⟩,⟨.covers 86,1,4⟩,⟨.covers 166,1,10⟩,⟨.covers 1062,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 2566,1,4⟩,⟨.covers 154,1,2⟩,⟨.covers 106,1,2⟩,⟨.covers 2090,1,1⟩,⟨.covers 2314,1,2⟩,⟨.covers 1546,1,5⟩,⟨.covers 210,1,5⟩,⟨.covers 1298,1,2⟩,⟨.covers 226,1,5⟩,⟨.covers 1122,1,3⟩,⟨.covers 92,1,10⟩,⟨.covers 156,1,3⟩,⟨.covers 172,1,7⟩,⟨.covers 1292,1,1⟩,⟨.covers 2316,1,7⟩,⟨.covers 1548,1,9⟩,⟨.covers 116,1,4⟩,⟨.covers 212,1,3⟩,⟨.covers 228,1,8⟩,⟨.covers 1796,1,4⟩,⟨.covers 2820,1,8⟩,⟨.covers 3588,1,4⟩,⟨.covers 120,1,2⟩,⟨.covers 184,1,4⟩,⟨.covers 1800,1,1⟩,⟨.covers 3336,1,5⟩,⟨.covers 3592,1,2⟩,⟨.covers 2160,1,1⟩,⟨.covers 2224,1,2⟩,⟨.covers 1616,1,1⟩,⟨.covers 1424,1,9⟩,⟨.covers 3360,1,1⟩,⟨.covers 3616,1,1⟩,⟨.covers 1728,1,1⟩,⟨.incident 2,8,-7⟩,⟨.incident 3,8,-3⟩]
def bound : Int := 6

theorem column_mask : listMask columns = restrictMask universeMask Source44.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source44.rootCodes link44 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual44_000
namespace C13.Global.FastDual44_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,11]
def points : Finset C13.Point := {2,3,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,883,885,886,889,890,892,947,979,995,1371,1395,1401,1402,1447,1461,1509,1639,1651,1653,1654,1691,1721,1753,1819,1831,1843,1845,1846,1849,1850,1852,1875,1881,1882,1891,1893,1894,1905,1906,1908,1912,1939,1945,1955,1957,1969,1987,2001,2017,2411,2419,2425,2455,2486,2518,2647,2675,2677,2731,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3187,3277,3278,3292,3308,3379,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816,3853,3861,3881,3889,3980,3988,4008,4016]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 2055,1,2⟩,⟨.covers 1035,1,1⟩,⟨.covers 2059,1,2⟩,⟨.covers 77,1,2⟩,⟨.covers 269,1,2⟩,⟨.covers 3089,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 270,1,2⟩,⟨.covers 1286,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 3106,1,1⟩,⟨.covers 156,1,2⟩,⟨.covers 172,1,2⟩,⟨.covers 116,1,1⟩,⟨.covers 180,1,2⟩,⟨.covers 1604,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 184,1,2⟩,⟨.covers 1352,1,1⟩,⟨.covers 720,1,2⟩,⟨.covers 2384,1,1⟩,⟨.covers 480,1,2⟩,⟨.covers 2656,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 2944,1,2⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source44.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source44.rootCodes link44 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual44_001
namespace C13.Global.FastDual44_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,8,9]
def points : Finset C13.Point := {2,3,8,9}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,829,830,892,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1401,1402,1447,1461,1462,1491,1498,1507,1509,1521,1522,1524,1528,1639,1653,1654,1691,1721,1722,1747,1753,1763,1766,1777,1778,1780,1784,1852,1987,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2425,2426,2455,2485,2486,2515,2518,2531,2537,2545,2546,2548,2552,2647,2677,2678,2731,2745,2746,2771,2773,2787,2794,2801,2802,2804,2808,2876,3011,3056,3187,3251,3271,3275,3277,3278,3283,3285,3286,3289,3290,3292,3299,3301,3302,3305,3306,3308,3313,3314,3316,3320,3403,3418,3433,3448,3463,3478,3493,3508,3523,3538,3553,3568,3655,3669,3686,3700,3723,3737,3754,3768,3779,3793,3810,3824]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 263,1,8⟩,⟨.covers 139,1,6⟩,⟨.covers 267,1,5⟩,⟨.covers 523,1,5⟩,⟨.covers 269,1,22⟩,⟨.covers 1037,1,16⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,4⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,7⟩,⟨.covers 89,1,4⟩,⟨.covers 1289,1,4⟩,⟨.covers 2569,1,6⟩,⟨.covers 2097,1,5⟩,⟨.covers 593,1,2⟩,⟨.covers 657,1,6⟩,⟨.covers 353,1,1⟩,⟨.covers 417,1,3⟩,⟨.covers 1313,1,2⟩,⟨.covers 1793,1,22⟩,⟨.covers 2817,1,22⟩,⟨.covers 270,1,22⟩,⟨.covers 1038,1,16⟩,⟨.covers 86,1,3⟩,⟨.covers 166,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 2566,1,5⟩,⟨.covers 154,1,1⟩,⟨.covers 106,1,3⟩,⟨.covers 2314,1,3⟩,⟨.covers 1546,1,2⟩,⟨.covers 1074,1,7⟩,⟨.covers 2098,1,4⟩,⟨.covers 338,1,1⟩,⟨.covers 402,1,3⟩,⟨.covers 610,1,3⟩,⟨.covers 674,1,5⟩,⟨.covers 108,1,5⟩,⟨.covers 172,1,1⟩,⟨.covers 1292,1,22⟩,⟨.covers 2316,1,22⟩,⟨.covers 596,1,5⟩,⟨.covers 2132,1,2⟩,⟨.covers 1124,1,4⟩,⟨.covers 1188,1,1⟩,⟨.covers 3332,1,3⟩,⟨.covers 3588,1,5⟩,⟨.covers 1112,1,3⟩,⟨.covers 1176,1,2⟩,⟨.covers 360,1,2⟩,⟨.covers 2152,1,2⟩,⟨.covers 2216,1,1⟩,⟨.covers 3336,1,5⟩,⟨.covers 3592,1,3⟩,⟨.covers 2256,1,2⟩,⟨.covers 848,1,10⟩,⟨.covers 1616,1,1⟩,⟨.covers 1424,1,4⟩,⟨.covers 2704,1,5⟩,⟨.covers 3344,1,4⟩,⟨.covers 2272,1,3⟩,⟨.covers 2656,1,1⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,6⟩,⟨.covers 3616,1,5⟩,⟨.incident 9,8,-7⟩]
def bound : Int := 17

theorem column_mask : listMask columns = restrictMask universeMask Source44.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source44.rootCodes link44 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual44_002
namespace C13.Global.FastDual44_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,8,9]
def points : Finset C13.Point := {2,7,8,9}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,892,971,979,995,1147,1261,1371,1387,1401,1402,1447,1453,1461,1509,1639,1646,1653,1654,1660,1691,1707,1721,1739,1753,1852,1987,2171,2270,2395,2411,2425,2426,2455,2462,2486,2518,2647,2653,2677,2678,2684,2715,2731,2746,2763,2794,2876,3011,3131,3163,3179,3187,3193,3194,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 71,1,5⟩,⟨.covers 139,1,2⟩,⟨.covers 267,1,4⟩,⟨.covers 2061,1,5⟩,⟨.covers 149,1,13⟩,⟨.covers 101,1,2⟩,⟨.covers 197,1,1⟩,⟨.covers 773,1,16⟩,⟨.covers 169,1,1⟩,⟨.covers 1289,1,4⟩,⟨.covers 2569,1,3⟩,⟨.covers 1553,1,1⟩,⟨.covers 2577,1,1⟩,⟨.covers 2145,1,4⟩,⟨.covers 1793,1,14⟩,⟨.covers 2817,1,5⟩,⟨.covers 3585,1,1⟩,⟨.covers 1038,1,6⟩,⟨.covers 774,1,7⟩,⟨.covers 1286,1,13⟩,⟨.covers 2566,1,3⟩,⟨.covers 1050,1,4⟩,⟨.covers 778,1,9⟩,⟨.covers 2314,1,4⟩,⟨.covers 1546,1,1⟩,⟨.covers 1570,1,2⟩,⟨.covers 2594,1,1⟩,⟨.covers 156,1,6⟩,⟨.covers 1292,1,9⟩,⟨.covers 2316,1,4⟩,⟨.covers 228,1,2⟩,⟨.covers 1796,1,8⟩,⟨.covers 2820,1,13⟩,⟨.covers 184,1,4⟩,⟨.covers 368,1,4⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,6⟩,⟨.covers 912,1,14⟩,⟨.covers 2704,1,1⟩,⟨.covers 480,1,2⟩,⟨.covers 2272,1,3⟩,⟨.covers 864,1,12⟩,⟨.covers 1376,1,4⟩,⟨.covers 2656,1,2⟩,⟨.covers 2464,1,13⟩,⟨.covers 1696,1,1⟩,⟨.covers 2496,1,9⟩,⟨.incident 2,8,-2⟩,⟨.incident 8,8,-7⟩,⟨.incident 9,8,-3⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source44.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source44.rootCodes link44 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual44_003
namespace C13.Global.FastDual44_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,8,11]
def points : Finset C13.Point := {2,7,8,11}
def columns : List Code := [379,439,631,635,637,638,699,731,747,829,830,859,875,889,890,892,971,979,995,1147,1261,1371,1387,1401,1402,1447,1453,1461,1509,1595,1627,1639,1643,1645,1646,1651,1653,1654,1657,1658,1660,1691,1707,1721,1739,1753,1769,1837,1852,1867,1882,1897,1912,1957,1987,2017,2171,2270,2411,2425,2455,2462,2486,2518,2619,2647,2653,2667,2675,2677,2681,2731,2746,2794,2921,2966,3131,3179,3187,3193,3277,3278,3292,3308,3433,3478,3627,3635,3661,3669,3689,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 1031,1,11⟩,⟨.covers 267,1,5⟩,⟨.covers 2059,1,5⟩,⟨.covers 1043,1,3⟩,⟨.covers 2563,1,5⟩,⟨.covers 2061,1,11⟩,⟨.covers 773,1,11⟩,⟨.covers 2309,1,11⟩,⟨.covers 2817,1,11⟩,⟨.covers 3329,1,11⟩,⟨.covers 270,1,5⟩,⟨.covers 1038,1,11⟩,⟨.covers 2566,1,5⟩,⟨.covers 1050,1,3⟩,⟨.covers 778,1,5⟩,⟨.covers 226,1,11⟩,⟨.covers 156,1,3⟩,⟨.covers 172,1,11⟩,⟨.covers 2316,1,3⟩,⟨.covers 116,1,11⟩,⟨.covers 180,1,3⟩,⟨.covers 2820,1,5⟩,⟨.covers 3332,1,11⟩,⟨.covers 184,1,11⟩,⟨.covers 1328,1,8⟩,⟨.covers 2352,1,8⟩,⟨.covers 720,1,11⟩,⟨.covers 2384,1,3⟩,⟨.covers 3152,1,8⟩,⟨.covers 1808,1,3⟩,⟨.covers 3600,1,3⟩,⟨.covers 1472,1,11⟩,⟨.covers 2496,1,8⟩,⟨.covers 3712,1,11⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source44.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source44.rootCodes link44 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual44_004
namespace C13.Global.FastDual44_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,11]
def points : Finset C13.Point := {2,7,9,11}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1387,1395,1401,1402,1447,1453,1461,1509,1639,1646,1653,1654,1660,1691,1707,1721,1739,1753,1838,1852,1894,1908,1931,1945,1987,2001,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2647,2653,2677,2731,2746,2794,2901,2986,3131,3179,3187,3193,3277,3278,3292,3308,3371,3379,3433,3441,3470,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 1031,1,5⟩,⟨.covers 2055,1,6⟩,⟨.covers 139,1,1⟩,⟨.covers 2059,1,4⟩,⟨.covers 1043,1,4⟩,⟨.covers 2307,1,4⟩,⟨.covers 1539,1,2⟩,⟨.covers 2563,1,10⟩,⟨.covers 141,1,2⟩,⟨.covers 269,1,3⟩,⟨.covers 149,1,3⟩,⟨.covers 197,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 777,1,4⟩,⟨.covers 3081,1,4⟩,⟨.covers 2817,1,16⟩,⟨.covers 3585,1,16⟩,⟨.covers 78,1,2⟩,⟨.covers 526,1,2⟩,⟨.covers 1094,1,2⟩,⟨.covers 774,1,5⟩,⟨.covers 3078,1,9⟩,⟨.covers 210,1,2⟩,⟨.covers 450,1,2⟩,⟨.covers 156,1,8⟩,⟨.covers 284,1,1⟩,⟨.covers 108,1,2⟩,⟨.covers 2316,1,4⟩,⟨.covers 2572,1,16⟩,⟨.covers 180,1,2⟩,⟨.covers 1176,1,1⟩,⟨.covers 360,1,4⟩,⟨.covers 1800,1,1⟩,⟨.covers 2824,1,8⟩,⟨.covers 3592,1,8⟩,⟨.covers 2160,1,4⟩,⟨.covers 2352,1,4⟩,⟨.covers 1584,1,6⟩,⟨.covers 720,1,2⟩,⟨.covers 912,1,2⟩,⟨.covers 2704,1,15⟩,⟨.covers 3216,1,4⟩,⟨.covers 480,1,4⟩,⟨.covers 864,1,2⟩,⟨.covers 3168,1,4⟩,⟨.covers 2464,1,7⟩,⟨.covers 3232,1,7⟩,⟨.covers 2496,1,9⟩,⟨.covers 1728,1,4⟩,⟨.covers 2752,1,15⟩,⟨.incident 2,8,-1⟩,⟨.incident 9,8,-3⟩,⟨.incident 11,8,-8⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source44.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source44.rootCodes link44 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual44_005
