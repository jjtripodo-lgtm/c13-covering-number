import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source43
namespace C13.Global.FastDual43_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,8]
def points : Finset C13.Point := {2,6,7,8}
def columns : List Code := [379,439,631,699,829,830,859,875,971,979,995,1371,1387,1402,1447,1453,1461,1595,1639,1646,1654,1691,1707,1721,1837,1852,1867,1882,1957,1987,2395,2411,2425,2455,2462,2486,2619,2647,2653,2677,2715,2731,2746,2846,2876,2891,2921,2966,3011,3131,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3611,3627,3635,3641,3642,3655,3661,3662,3669,3670,3676,3685,3686,3692,3700,3723,3737,3738,3753,3754,3768,3788]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 139,1,5⟩,⟨.covers 269,1,1⟩,⟨.covers 149,1,14⟩,⟨.covers 2069,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 197,1,18⟩,⟨.covers 89,1,1⟩,⟨.covers 1049,1,2⟩,⟨.covers 169,1,5⟩,⟨.covers 2337,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 166,1,1⟩,⟨.covers 1062,1,1⟩,⟨.covers 198,1,18⟩,⟨.covers 1286,1,14⟩,⟨.covers 154,1,5⟩,⟨.covers 106,1,3⟩,⟨.covers 210,1,18⟩,⟨.covers 1106,1,1⟩,⟨.covers 226,1,18⟩,⟨.covers 2210,1,3⟩,⟨.covers 2594,1,2⟩,⟨.covers 92,1,2⟩,⟨.covers 156,1,9⟩,⟨.covers 172,1,9⟩,⟨.covers 212,1,7⟩,⟨.covers 228,1,10⟩,⟨.covers 3332,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 2384,1,3⟩,⟨.covers 1616,1,3⟩,⟨.covers 1424,1,1⟩,⟨.covers 2704,1,5⟩,⟨.covers 2656,1,2⟩,⟨.covers 2464,1,11⟩,⟨.covers 1696,1,5⟩,⟨.covers 2848,1,2⟩,⟨.covers 3360,1,1⟩,⟨.covers 1472,1,7⟩,⟨.covers 2496,1,8⟩,⟨.covers 1856,1,1⟩,⟨.covers 1920,1,10⟩,⟨.covers 2944,1,10⟩,⟨.covers 3712,1,5⟩,⟨.incident 6,8,-3⟩,⟨.incident 7,8,-14⟩]
def bound : Int := 3

theorem column_mask : listMask columns = restrictMask universeMask Source43.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source43.rootCodes link43 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual43_008
namespace C13.Global.FastDual43_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,9]
def points : Finset C13.Point := {2,6,7,9}
def columns : List Code := [379,439,631,699,829,830,923,939,971,979,995,1339,1371,1387,1402,1447,1453,1461,1639,1646,1654,1691,1707,1721,1838,1852,1894,1931,1945,1987,2363,2395,2411,2425,2455,2462,2486,2647,2653,2677,2715,2731,2746,2845,2876,2901,2955,2986,3011,3131,3277,3278,3292,3308,3355,3371,3379,3385,3386,3403,3417,3418,3433,3434,3448,3463,3469,3470,3477,3478,3484,3493,3494,3500,3508,3532,3655,3669,3686,3700,3723,3737,3754,3768,3853,3884,3909,3940,3977,4008,4033,4064]
def rows : List LinearRow := [⟨.covers 75,1,6⟩,⟨.covers 101,1,25⟩,⟨.covers 197,1,6⟩,⟨.covers 89,1,6⟩,⟨.covers 201,1,19⟩,⟨.covers 198,1,25⟩,⟨.covers 2566,1,25⟩,⟨.covers 106,1,6⟩,⟨.covers 210,1,25⟩,⟨.covers 226,1,25⟩,⟨.covers 1346,1,6⟩,⟨.covers 92,1,19⟩,⟨.covers 212,1,6⟩,⟨.covers 228,1,25⟩,⟨.covers 120,1,6⟩,⟨.covers 1352,1,6⟩,⟨.covers 2376,1,6⟩,⟨.covers 2384,1,6⟩,⟨.covers 1616,1,25⟩,⟨.covers 1856,1,6⟩,⟨.covers 2880,1,19⟩,⟨.incident 6,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source43.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source43.rootCodes link43 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual43_009
namespace C13.Global.FastDual43_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,11]
def points : Finset C13.Point := {2,6,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,859,875,883,923,939,947,971,979,995,1339,1371,1387,1402,1447,1453,1461,1595,1639,1646,1654,1691,1707,1721,1819,1831,1835,1837,1838,1843,1845,1846,1849,1850,1852,1867,1875,1882,1891,1894,1898,1906,1931,1939,1945,1955,1957,1961,1969,1987,2363,2411,2425,2455,2462,2486,2619,2647,2653,2677,2731,2746,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3277,3278,3292,3308,3371,3379,3433,3470,3478,3532,3627,3635,3661,3669,3754,3788]
def rows : List LinearRow := [⟨.covers 135,1,3⟩,⟨.covers 1031,1,8⟩,⟨.covers 2055,1,8⟩,⟨.covers 75,1,6⟩,⟨.covers 139,1,6⟩,⟨.covers 2059,1,3⟩,⟨.covers 141,1,6⟩,⟨.covers 269,1,3⟩,⟨.covers 525,1,6⟩,⟨.covers 101,1,3⟩,⟨.covers 197,1,6⟩,⟨.covers 1049,1,3⟩,⟨.covers 169,1,3⟩,⟨.covers 3089,1,3⟩,⟨.covers 3329,1,8⟩,⟨.covers 3585,1,6⟩,⟨.covers 78,1,8⟩,⟨.covers 270,1,8⟩,⟨.covers 86,1,3⟩,⟨.covers 3078,1,3⟩,⟨.covers 1050,1,3⟩,⟨.covers 106,1,3⟩,⟨.covers 210,1,11⟩,⟨.covers 226,1,11⟩,⟨.covers 92,1,3⟩,⟨.covers 156,1,3⟩,⟨.covers 540,1,3⟩,⟨.covers 116,1,6⟩,⟨.covers 180,1,8⟩,⟨.covers 212,1,6⟩,⟨.covers 228,1,11⟩,⟨.covers 1796,1,3⟩,⟨.covers 2820,1,3⟩,⟨.covers 120,1,3⟩,⟨.covers 184,1,3⟩,⟨.covers 2824,1,8⟩,⟨.covers 2384,1,8⟩,⟨.covers 1616,1,3⟩,⟨.covers 1424,1,3⟩,⟨.covers 2704,1,8⟩,⟨.covers 1376,1,3⟩,⟨.covers 2656,1,3⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,3⟩,⟨.covers 3616,1,3⟩,⟨.covers 2496,1,11⟩,⟨.covers 2752,1,6⟩,⟨.covers 1856,1,6⟩,⟨.covers 1920,1,6⟩,⟨.covers 3712,1,6⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source43.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source43.rootCodes link43 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual43_010
namespace C13.Global.FastDual43_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,8,9]
def points : Finset C13.Point := {2,6,8,9}
def columns : List Code := [254,379,439,445,446,475,491,506,631,699,758,829,830,956,971,979,995,1010,1211,1262,1371,1387,1402,1447,1453,1461,1462,1468,1483,1498,1639,1646,1654,1691,1707,1721,1722,1766,1852,1987,2235,2269,2300,2395,2411,2425,2455,2462,2485,2486,2492,2507,2537,2552,2647,2653,2677,2715,2731,2745,2746,2773,2804,2876,3011,3056,3131,3227,3243,3251,3257,3258,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 525,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 2062,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 1616,1,1⟩,⟨.incident 2,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source43.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source43.rootCodes link43 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual43_011
namespace C13.Global.FastDual43_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,8,11]
def points : Finset C13.Point := {2,6,8,11}
def columns : List Code := [254,379,439,445,446,475,491,506,631,699,758,829,830,859,875,949,950,956,971,979,995,1010,1211,1262,1371,1387,1402,1447,1453,1461,1462,1468,1483,1498,1595,1639,1646,1654,1691,1707,1715,1721,1722,1766,1837,1852,1867,1882,1957,1972,1987,2002,2235,2269,2300,2411,2425,2455,2462,2486,2537,2552,2619,2647,2653,2677,2731,2739,2746,2773,2804,2921,2966,3056,3131,3243,3251,3258,3277,3278,3292,3308,3433,3478,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 2059,1,6⟩,⟨.covers 2307,1,19⟩,⟨.covers 2563,1,6⟩,⟨.covers 197,1,25⟩,⟨.covers 2309,1,6⟩,⟨.covers 2097,1,6⟩,⟨.covers 2817,1,25⟩,⟨.covers 3329,1,6⟩,⟨.covers 2062,1,19⟩,⟨.covers 2566,1,19⟩,⟨.covers 3082,1,6⟩,⟨.covers 2098,1,6⟩,⟨.covers 2210,1,6⟩,⟨.covers 2316,1,6⟩,⟨.covers 2572,1,25⟩,⟨.covers 2820,1,6⟩,⟨.covers 3332,1,25⟩,⟨.covers 2160,1,12⟩,⟨.covers 3152,1,25⟩,⟨.covers 3168,1,19⟩,⟨.covers 2464,1,12⟩,⟨.covers 3232,1,6⟩,⟨.covers 3616,1,6⟩,⟨.incident 11,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source43.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source43.rootCodes link43 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual43_012
namespace C13.Global.FastDual43_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,9,11]
def points : Finset C13.Point := {2,6,9,11}
def columns : List Code := [254,379,439,443,445,446,475,491,506,631,699,758,829,830,923,939,953,954,956,971,979,995,1010,1211,1262,1339,1371,1387,1402,1435,1447,1451,1453,1454,1459,1461,1462,1465,1466,1468,1483,1498,1514,1639,1646,1654,1691,1707,1721,1722,1766,1838,1852,1894,1931,1945,1962,1976,1987,2018,2235,2269,2300,2363,2411,2425,2455,2462,2475,2483,2486,2490,2537,2552,2647,2653,2677,2731,2746,2773,2804,2901,2986,3056,3131,3243,3251,3258,3277,3278,3292,3308,3371,3379,3433,3470,3478,3498,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 135,1,8⟩,⟨.covers 523,1,8⟩,⟨.covers 2059,1,9⟩,⟨.covers 1043,1,3⟩,⟨.covers 2307,1,5⟩,⟨.covers 269,1,8⟩,⟨.covers 101,1,13⟩,⟨.covers 197,1,13⟩,⟨.covers 1049,1,3⟩,⟨.covers 777,1,5⟩,⟨.covers 2569,1,3⟩,⟨.covers 353,1,1⟩,⟨.covers 2817,1,20⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,20⟩,⟨.covers 78,1,6⟩,⟨.covers 2062,1,5⟩,⟨.covers 774,1,13⟩,⟨.covers 2566,1,20⟩,⟨.covers 3078,1,2⟩,⟨.covers 2098,1,1⟩,⟨.covers 210,1,2⟩,⟨.covers 1106,1,3⟩,⟨.covers 1100,1,2⟩,⟨.covers 2316,1,8⟩,⟨.covers 2572,1,16⟩,⟨.covers 2196,1,2⟩,⟨.covers 2824,1,20⟩,⟨.covers 3592,1,20⟩,⟨.covers 368,1,3⟩,⟨.covers 1328,1,3⟩,⟨.covers 1584,1,10⟩,⟨.covers 2608,1,7⟩,⟨.covers 464,1,3⟩,⟨.covers 2704,1,5⟩,⟨.covers 3216,1,11⟩,⟨.covers 2272,1,2⟩,⟨.covers 3168,1,11⟩,⟨.covers 1728,1,13⟩,⟨.covers 3392,1,2⟩,⟨.incident 9,8,-5⟩,⟨.incident 11,8,-7⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source43.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source43.rootCodes link43 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual43_013
namespace C13.Global.FastDual43_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,8,9]
def points : Finset C13.Point := {2,7,8,9}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,892,971,979,995,1147,1261,1371,1387,1401,1402,1447,1453,1461,1509,1639,1646,1653,1654,1660,1691,1707,1721,1739,1753,1852,1987,2171,2270,2395,2411,2425,2426,2455,2462,2486,2518,2647,2653,2677,2678,2684,2715,2731,2746,2763,2794,2876,3011,3131,3163,3179,3187,3193,3194,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 71,1,5⟩,⟨.covers 139,1,2⟩,⟨.covers 267,1,4⟩,⟨.covers 141,1,1⟩,⟨.covers 269,1,5⟩,⟨.covers 2061,1,5⟩,⟨.covers 149,1,13⟩,⟨.covers 101,1,2⟩,⟨.covers 773,1,2⟩,⟨.covers 169,1,1⟩,⟨.covers 777,1,9⟩,⟨.covers 1289,1,4⟩,⟨.covers 2569,1,3⟩,⟨.covers 1553,1,1⟩,⟨.covers 2577,1,1⟩,⟨.covers 2145,1,4⟩,⟨.covers 1793,1,7⟩,⟨.covers 2817,1,14⟩,⟨.covers 3585,1,1⟩,⟨.covers 270,1,4⟩,⟨.covers 1038,1,6⟩,⟨.covers 774,1,13⟩,⟨.covers 1286,1,13⟩,⟨.covers 2566,1,3⟩,⟨.covers 1050,1,4⟩,⟨.covers 2314,1,4⟩,⟨.covers 1546,1,1⟩,⟨.covers 1570,1,2⟩,⟨.covers 2594,1,1⟩,⟨.covers 156,1,6⟩,⟨.covers 172,1,2⟩,⟨.covers 1796,1,16⟩,⟨.covers 2820,1,16⟩,⟨.covers 184,1,4⟩,⟨.covers 368,1,4⟩,⟨.covers 464,1,9⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,6⟩,⟨.covers 912,1,5⟩,⟨.covers 2704,1,1⟩,⟨.covers 2272,1,3⟩,⟨.covers 1376,1,4⟩,⟨.covers 2656,1,2⟩,⟨.covers 928,1,14⟩,⟨.covers 2464,1,13⟩,⟨.covers 1696,1,1⟩,⟨.covers 1472,1,8⟩,⟨.incident 2,8,-2⟩,⟨.incident 8,8,-7⟩,⟨.incident 9,8,-3⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source43.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source43.rootCodes link43 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual43_014
namespace C13.Global.FastDual43_015
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,8,11]
def points : Finset C13.Point := {2,7,8,11}
def columns : List Code := [379,439,631,635,637,638,699,731,747,829,830,859,875,889,890,892,971,979,995,1147,1261,1371,1387,1401,1402,1447,1453,1461,1509,1595,1627,1639,1643,1645,1646,1651,1653,1654,1657,1658,1660,1691,1707,1721,1739,1753,1769,1837,1852,1867,1882,1897,1912,1957,1987,2017,2171,2270,2411,2425,2455,2462,2486,2518,2619,2647,2653,2667,2675,2677,2681,2731,2746,2794,2921,2966,3131,3179,3187,3193,3277,3278,3292,3308,3433,3478,3627,3635,3661,3669,3689,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 773,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 1038,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3332,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 1328,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 3712,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source43.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source43.rootCodes link43 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual43_015
