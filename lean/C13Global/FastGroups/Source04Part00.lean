import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source04
namespace C13.Global.FastDual04_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,8]
def points : Finset C13.Point := {2,3,7,8}
def columns : List Code := [379,439,631,699,829,830,889,890,892,979,995,1371,1401,1402,1447,1461,1509,1639,1651,1653,1654,1691,1721,1753,1852,1882,1912,1957,1987,2017,2411,2425,2426,2455,2486,2518,2647,2675,2677,2678,2731,2746,2794,2876,2921,2936,2966,3011,3026,3187,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3635,3655,3667,3669,3670,3683,3685,3686,3697,3698,3700,3723,3737,3738,3753,3754,3768,3785,3786,3788,3800,3816]
def rows : List LinearRow := [⟨.covers 77,1,2⟩,⟨.covers 269,1,1⟩,⟨.covers 773,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 78,1,2⟩,⟨.covers 270,1,1⟩,⟨.covers 166,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 1292,1,2⟩,⟨.covers 2316,1,2⟩,⟨.covers 212,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 1424,1,1⟩,⟨.incident 2,8,-1⟩,⟨.incident 3,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source04.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source04.rootCodes link04 points rows bound = true := by decide +kernel

end C13.Global.FastDual04_000
namespace C13.Global.FastDual04_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,10]
def points : Finset C13.Point := {2,3,7,10}
def columns : List Code := [379,439,631,699,823,827,829,830,883,885,886,889,890,892,947,979,995,1371,1395,1402,1447,1461,1509,1639,1651,1654,1691,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2411,2419,2425,2426,2455,2486,2518,2647,2675,2677,2678,2731,2746,2794,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2902,2915,2921,2922,2929,2930,2932,2936,2963,2966,2979,2986,2994,3011,3026,3042,3187,3277,3278,3292,3308,3379,3418,3442,3493,3532,3556,3635,3686,3698,3737,3788,3800,3854,3866,3878,3890,3980,3992,4004,4016]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 77,1,2⟩,⟨.covers 269,1,2⟩,⟨.covers 2309,1,1⟩,⟨.covers 1541,1,2⟩,⟨.covers 1289,1,2⟩,⟨.covers 2569,1,1⟩,⟨.covers 3089,1,1⟩,⟨.covers 78,1,2⟩,⟨.covers 270,1,2⟩,⟨.covers 166,1,2⟩,⟨.covers 154,1,2⟩,⟨.covers 3106,1,1⟩,⟨.covers 156,1,2⟩,⟨.covers 172,1,2⟩,⟨.covers 116,1,1⟩,⟨.covers 2628,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 2376,1,1⟩,⟨.covers 1200,1,2⟩,⟨.covers 464,1,2⟩,⟨.covers 1616,1,1⟩,⟨.covers 736,1,2⟩,⟨.covers 1376,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source04.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source04.rootCodes link04 points rows bound = true := by decide +kernel

end C13.Global.FastDual04_001
namespace C13.Global.FastDual04_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,11]
def points : Finset C13.Point := {2,3,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,883,885,886,889,890,892,947,979,995,1371,1395,1401,1402,1447,1461,1509,1639,1651,1653,1654,1691,1721,1753,1819,1831,1843,1845,1846,1849,1850,1852,1875,1881,1882,1891,1893,1894,1905,1906,1908,1912,1939,1945,1955,1957,1969,1987,2001,2017,2411,2419,2425,2455,2486,2518,2647,2675,2677,2731,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3187,3277,3278,3292,3308,3379,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 135,1,3⟩,⟨.covers 2055,1,3⟩,⟨.covers 75,1,3⟩,⟨.covers 139,1,3⟩,⟨.covers 77,1,3⟩,⟨.covers 269,1,11⟩,⟨.covers 2309,1,5⟩,⟨.covers 1541,1,5⟩,⟨.covers 3077,1,5⟩,⟨.covers 1289,1,5⟩,⟨.covers 2569,1,8⟩,⟨.covers 3081,1,3⟩,⟨.covers 78,1,8⟩,⟨.covers 270,1,11⟩,⟨.covers 86,1,3⟩,⟨.covers 166,1,8⟩,⟨.covers 2566,1,3⟩,⟨.covers 3078,1,3⟩,⟨.covers 154,1,8⟩,⟨.covers 106,1,5⟩,⟨.covers 2314,1,3⟩,⟨.covers 1346,1,3⟩,⟨.covers 1602,1,3⟩,⟨.covers 3330,1,8⟩,⟨.covers 3586,1,5⟩,⟨.covers 92,1,3⟩,⟨.covers 156,1,5⟩,⟨.covers 172,1,8⟩,⟨.covers 2316,1,11⟩,⟨.covers 2572,1,11⟩,⟨.covers 116,1,5⟩,⟨.covers 228,1,3⟩,⟨.covers 1796,1,5⟩,⟨.covers 120,1,3⟩,⟨.covers 216,1,3⟩,⟨.covers 1800,1,5⟩,⟨.covers 2160,1,3⟩,⟨.covers 1200,1,11⟩,⟨.covers 2224,1,3⟩,⟨.covers 464,1,3⟩,⟨.covers 720,1,8⟩,⟨.covers 2384,1,5⟩,⟨.covers 480,1,8⟩,⟨.covers 736,1,3⟩,⟨.covers 2656,1,3⟩,⟨.covers 3360,1,3⟩,⟨.covers 3616,1,5⟩,⟨.covers 2944,1,8⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source04.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source04.rootCodes link04 points rows bound = true := by decide +kernel

end C13.Global.FastDual04_002
namespace C13.Global.FastDual04_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,8,9]
def points : Finset C13.Point := {2,3,8,9}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,829,830,892,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1401,1402,1447,1461,1462,1491,1498,1507,1509,1521,1522,1524,1528,1639,1653,1654,1691,1721,1722,1747,1753,1763,1766,1777,1778,1780,1784,1852,1987,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2425,2426,2455,2485,2486,2515,2518,2531,2537,2545,2546,2548,2552,2647,2677,2678,2731,2745,2746,2771,2773,2787,2794,2801,2802,2804,2808,2876,3011,3056,3187,3251,3271,3275,3277,3278,3283,3285,3286,3289,3290,3292,3299,3301,3302,3305,3306,3308,3313,3314,3316,3320,3403,3418,3433,3448,3463,3478,3493,3508,3523,3538,3553,3568,3655,3669,3686,3700,3723,3737,3754,3768,3779,3793,3810,3824]
def rows : List LinearRow := [⟨.covers 135,1,6⟩,⟨.covers 519,1,8⟩,⟨.covers 75,1,2⟩,⟨.covers 267,1,6⟩,⟨.covers 523,1,6⟩,⟨.covers 269,1,20⟩,⟨.covers 1037,1,20⟩,⟨.covers 149,1,4⟩,⟨.covers 101,1,2⟩,⟨.covers 2309,1,3⟩,⟨.covers 1541,1,7⟩,⟨.covers 89,1,6⟩,⟨.covers 169,1,1⟩,⟨.covers 1289,1,2⟩,⟨.covers 2569,1,8⟩,⟨.covers 1073,1,4⟩,⟨.covers 2097,1,5⟩,⟨.covers 593,1,4⟩,⟨.covers 657,1,1⟩,⟨.covers 353,1,2⟩,⟨.covers 417,1,1⟩,⟨.covers 2337,1,1⟩,⟨.covers 270,1,20⟩,⟨.covers 1038,1,20⟩,⟨.covers 86,1,1⟩,⟨.covers 166,1,5⟩,⟨.covers 1286,1,3⟩,⟨.covers 2566,1,1⟩,⟨.covers 154,1,7⟩,⟨.covers 2314,1,5⟩,⟨.covers 1546,1,1⟩,⟨.covers 1074,1,4⟩,⟨.covers 2098,1,5⟩,⟨.covers 338,1,3⟩,⟨.covers 402,1,3⟩,⟨.covers 2322,1,1⟩,⟨.covers 610,1,2⟩,⟨.covers 674,1,1⟩,⟨.covers 2594,1,3⟩,⟨.covers 1794,1,20⟩,⟨.covers 2818,1,20⟩,⟨.covers 108,1,6⟩,⟨.covers 172,1,1⟩,⟨.covers 1292,1,20⟩,⟨.covers 2316,1,20⟩,⟨.covers 596,1,2⟩,⟨.covers 2132,1,3⟩,⟨.covers 2196,1,2⟩,⟨.covers 1188,1,4⟩,⟨.covers 3332,1,7⟩,⟨.covers 3588,1,3⟩,⟨.covers 344,1,1⟩,⟨.covers 1112,1,1⟩,⟨.covers 664,1,2⟩,⟨.covers 1176,1,3⟩,⟨.covers 2152,1,4⟩,⟨.covers 680,1,1⟩,⟨.covers 3336,1,6⟩,⟨.covers 3592,1,5⟩,⟨.covers 1232,1,3⟩,⟨.covers 2256,1,3⟩,⟨.covers 3344,1,3⟩,⟨.covers 1248,1,3⟩,⟨.covers 864,1,10⟩,⟨.covers 1376,1,4⟩,⟨.covers 2656,1,3⟩,⟨.covers 2464,1,3⟩,⟨.covers 3360,1,1⟩,⟨.covers 3616,1,8⟩]
def bound : Int := 22

theorem column_mask : listMask columns = restrictMask universeMask Source04.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source04.rootCodes link04 points rows bound = true := by decide +kernel

end C13.Global.FastDual04_003
namespace C13.Global.FastDual04_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,10,11]
def points : Finset C13.Point := {2,3,10,11}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,823,827,829,830,883,885,886,889,890,892,947,949,950,953,954,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1395,1402,1447,1459,1461,1497,1498,1509,1510,1521,1522,1524,1528,1639,1651,1654,1691,1715,1721,1753,1754,1765,1766,1777,1778,1780,1784,1819,1831,1843,1882,1894,1906,1945,1957,1969,2008,2020,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2419,2425,2455,2483,2486,2517,2518,2537,2538,2545,2546,2548,2552,2647,2675,2677,2731,2739,2746,2773,2774,2793,2794,2801,2802,2804,2808,2839,2859,2867,2901,2921,2929,2966,2986,2994,3028,3048,3056,3187,3251,3277,3278,3292,3308,3313,3314,3316,3320,3379,3532,3568,3635,3788,3824]
def rows : List LinearRow := [⟨.covers 139,1,1⟩,⟨.covers 269,1,2⟩,⟨.covers 1037,1,2⟩,⟨.covers 2309,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 1289,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 705,1,1⟩,⟨.covers 270,1,2⟩,⟨.covers 1038,1,2⟩,⟨.covers 86,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 450,1,1⟩,⟨.covers 3330,1,2⟩,⟨.covers 3586,1,2⟩,⟨.covers 172,1,1⟩,⟨.covers 1292,1,2⟩,⟨.covers 1548,1,2⟩,⟨.covers 3152,1,1⟩,⟨.covers 1920,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source04.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source04.rootCodes link04 points rows bound = true := by decide +kernel

end C13.Global.FastDual04_004
namespace C13.Global.FastDual04_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,8,9]
def points : Finset C13.Point := {2,7,8,9}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,892,971,979,995,1147,1261,1371,1387,1401,1402,1447,1453,1461,1509,1639,1646,1653,1654,1660,1691,1707,1721,1739,1753,1852,1987,2171,2270,2395,2411,2425,2426,2455,2462,2486,2518,2647,2653,2677,2678,2684,2715,2731,2746,2763,2794,2876,3011,3131,3163,3179,3187,3193,3194,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 1043,1,3⟩,⟨.covers 2061,1,7⟩,⟨.covers 149,1,7⟩,⟨.covers 101,1,3⟩,⟨.covers 773,1,14⟩,⟨.covers 1541,1,3⟩,⟨.covers 169,1,4⟩,⟨.covers 2089,1,1⟩,⟨.covers 1289,1,1⟩,⟨.covers 2569,1,5⟩,⟨.covers 2097,1,3⟩,⟨.covers 1553,1,2⟩,⟨.covers 2577,1,2⟩,⟨.covers 1038,1,7⟩,⟨.covers 86,1,4⟩,⟨.covers 774,1,2⟩,⟨.covers 1286,1,7⟩,⟨.covers 2566,1,2⟩,⟨.covers 154,1,3⟩,⟨.covers 778,1,12⟩,⟨.covers 2314,1,4⟩,⟨.covers 1546,1,5⟩,⟨.covers 1106,1,1⟩,⟨.covers 1570,1,2⟩,⟨.covers 2594,1,2⟩,⟨.covers 1794,1,14⟩,⟨.covers 2818,1,14⟩,⟨.covers 3586,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 1796,1,12⟩,⟨.covers 2820,1,14⟩,⟨.covers 3588,1,2⟩,⟨.covers 120,1,1⟩,⟨.covers 184,1,6⟩,⟨.covers 3592,1,2⟩,⟨.covers 464,1,1⟩,⟨.covers 1232,1,7⟩,⟨.covers 848,1,11⟩,⟨.covers 2384,1,1⟩,⟨.covers 1616,1,5⟩,⟨.covers 912,1,1⟩,⟨.covers 2704,1,3⟩,⟨.covers 2272,1,7⟩,⟨.covers 1376,1,4⟩,⟨.covers 2656,1,5⟩,⟨.covers 928,1,14⟩,⟨.covers 2464,1,7⟩,⟨.covers 1696,1,2⟩,⟨.incident 9,8,-7⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source04.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source04.rootCodes link04 points rows bound = true := by decide +kernel

end C13.Global.FastDual04_005
namespace C13.Global.FastDual04_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,8,10]
def points : Finset C13.Point := {2,7,8,10}
def columns : List Code := [379,439,631,635,637,638,699,731,747,829,830,859,875,889,890,892,971,979,995,1147,1261,1371,1402,1447,1453,1461,1509,1595,1627,1639,1646,1651,1654,1658,1691,1721,1753,1882,1957,2171,2270,2395,2411,2425,2426,2455,2462,2486,2518,2619,2647,2651,2653,2654,2667,2675,2677,2678,2681,2682,2684,2715,2731,2746,2763,2778,2794,2846,2876,2891,2906,2921,2936,2966,3011,3026,3131,3163,3187,3194,3277,3278,3292,3308,3418,3493,3611,3635,3662,3674,3686,3698,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 1283,1,1⟩,⟨.covers 2307,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 3332,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 912,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 480,1,1⟩,⟨.covers 2272,1,1⟩,⟨.covers 3712,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source04.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source04.rootCodes link04 points rows bound = true := by decide +kernel

end C13.Global.FastDual04_006
namespace C13.Global.FastDual04_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,8,11]
def points : Finset C13.Point := {2,7,8,11}
def columns : List Code := [379,439,631,635,637,638,699,731,747,829,830,859,875,889,890,892,971,979,995,1147,1261,1371,1387,1401,1402,1447,1453,1461,1509,1595,1627,1639,1643,1645,1646,1651,1653,1654,1657,1658,1660,1691,1707,1721,1739,1753,1769,1837,1852,1867,1882,1897,1912,1957,1987,2017,2171,2270,2411,2425,2455,2462,2486,2518,2619,2647,2653,2667,2675,2677,2681,2731,2746,2794,2921,2966,3131,3179,3187,3193,3277,3278,3292,3308,3433,3478,3627,3635,3661,3669,3689,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 1031,1,8⟩,⟨.covers 139,1,3⟩,⟨.covers 267,1,2⟩,⟨.covers 2059,1,8⟩,⟨.covers 1043,1,3⟩,⟨.covers 1283,1,2⟩,⟨.covers 141,1,5⟩,⟨.covers 533,1,1⟩,⟨.covers 197,1,2⟩,⟨.covers 773,1,8⟩,⟨.covers 2309,1,12⟩,⟨.covers 3077,1,3⟩,⟨.covers 526,1,2⟩,⟨.covers 1038,1,8⟩,⟨.covers 2566,1,8⟩,⟨.covers 1050,1,1⟩,⟨.covers 202,1,4⟩,⟨.covers 1106,1,1⟩,⟨.covers 674,1,1⟩,⟨.covers 1794,1,5⟩,⟨.covers 3330,1,12⟩,⟨.covers 3586,1,4⟩,⟨.covers 92,1,1⟩,⟨.covers 172,1,3⟩,⟨.covers 1292,1,2⟩,⟨.covers 2316,1,12⟩,⟨.covers 2572,1,9⟩,⟨.covers 116,1,6⟩,⟨.covers 184,1,5⟩,⟨.covers 2824,1,12⟩,⟨.covers 3336,1,12⟩,⟨.covers 368,1,2⟩,⟨.covers 2160,1,4⟩,⟨.covers 1200,1,4⟩,⟨.covers 1328,1,5⟩,⟨.covers 464,1,6⟩,⟨.covers 720,1,2⟩,⟨.covers 1232,1,8⟩,⟨.covers 2384,1,5⟩,⟨.covers 3152,1,3⟩,⟨.covers 912,1,1⟩,⟨.covers 2704,1,3⟩,⟨.covers 1808,1,2⟩,⟨.covers 3600,1,4⟩,⟨.covers 480,1,8⟩,⟨.covers 2272,1,6⟩,⟨.covers 2464,1,12⟩,⟨.covers 3232,1,3⟩,⟨.covers 1920,1,2⟩,⟨.covers 3712,1,3⟩,⟨.incident 11,8,-2⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source04.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source04.rootCodes link04 points rows bound = true := by decide +kernel

end C13.Global.FastDual04_007
