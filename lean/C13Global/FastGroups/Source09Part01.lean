import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source09
namespace C13.Global.FastDual09_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,11]
def points : Finset C13.Point := {2,6,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,859,875,883,923,939,947,971,979,995,1339,1371,1387,1402,1447,1453,1461,1595,1639,1646,1654,1691,1707,1721,1819,1831,1835,1837,1838,1843,1845,1846,1849,1850,1852,1867,1875,1882,1891,1894,1898,1906,1931,1939,1945,1955,1957,1961,1969,1987,2363,2411,2425,2455,2462,2486,2619,2647,2653,2677,2731,2746,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3277,3278,3292,3308,3371,3379,3433,3470,3478,3532,3627,3635,3661,3669,3754,3788]
def rows : List LinearRow := [⟨.covers 1031,1,10⟩,⟨.covers 2055,1,4⟩,⟨.covers 75,1,4⟩,⟨.covers 139,1,4⟩,⟨.covers 1035,1,1⟩,⟨.covers 2059,1,2⟩,⟨.covers 269,1,10⟩,⟨.covers 149,1,6⟩,⟨.covers 197,1,8⟩,⟨.covers 89,1,3⟩,⟨.covers 201,1,2⟩,⟨.covers 2569,1,4⟩,⟨.covers 142,1,3⟩,⟨.covers 526,1,10⟩,⟨.covers 198,1,4⟩,⟨.covers 2566,1,6⟩,⟨.covers 154,1,3⟩,⟨.covers 2314,1,4⟩,⟨.covers 3082,1,3⟩,⟨.covers 210,1,11⟩,⟨.covers 226,1,11⟩,⟨.covers 92,1,3⟩,⟨.covers 116,1,10⟩,⟨.covers 180,1,4⟩,⟨.covers 212,1,7⟩,⟨.covers 228,1,5⟩,⟨.covers 120,1,3⟩,⟨.covers 184,1,3⟩,⟨.covers 1304,1,2⟩,⟨.covers 1560,1,2⟩,⟨.covers 2384,1,4⟩,⟨.covers 2704,1,4⟩,⟨.covers 3344,1,10⟩,⟨.covers 3600,1,10⟩,⟨.covers 1376,1,5⟩,⟨.covers 3168,1,6⟩,⟨.covers 2464,1,6⟩,⟨.covers 1696,1,5⟩,⟨.covers 2496,1,11⟩,⟨.covers 2752,1,9⟩,⟨.covers 1856,1,5⟩,⟨.covers 2880,1,6⟩,⟨.covers 1920,1,5⟩,⟨.covers 3712,1,2⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_008
namespace C13.Global.FastDual09_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,8,9]
def points : Finset C13.Point := {2,6,8,9}
def columns : List Code := [254,379,439,445,446,475,491,506,631,699,758,829,830,956,971,979,995,1010,1211,1262,1371,1387,1402,1447,1453,1461,1462,1468,1483,1498,1639,1646,1654,1691,1707,1721,1722,1766,1852,1987,2235,2269,2300,2395,2411,2425,2455,2462,2485,2486,2492,2507,2537,2552,2647,2653,2677,2715,2731,2745,2746,2773,2804,2876,3011,3056,3131,3227,3243,3251,3257,3258,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 525,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 2062,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 1616,1,1⟩,⟨.incident 2,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_009
namespace C13.Global.FastDual09_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,8,11]
def points : Finset C13.Point := {2,6,8,11}
def columns : List Code := [254,379,439,445,446,475,491,506,631,699,758,829,830,859,875,949,950,956,971,979,995,1010,1211,1262,1371,1387,1402,1447,1453,1461,1462,1468,1483,1498,1595,1639,1646,1654,1691,1707,1715,1721,1722,1766,1837,1852,1867,1882,1957,1972,1987,2002,2235,2269,2300,2411,2425,2455,2462,2486,2537,2552,2619,2647,2653,2677,2731,2739,2746,2773,2804,2921,2966,3056,3131,3243,3251,3258,3277,3278,3292,3308,3433,3478,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 2059,1,1⟩,⟨.covers 197,1,2⟩,⟨.covers 2309,1,2⟩,⟨.covers 2097,1,1⟩,⟨.covers 2566,1,2⟩,⟨.covers 3078,1,2⟩,⟨.covers 2316,1,2⟩,⟨.covers 2572,1,2⟩,⟨.covers 2824,1,2⟩,⟨.covers 3336,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 3152,1,2⟩,⟨.covers 3168,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 3616,1,1⟩,⟨.incident 11,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_010
namespace C13.Global.FastDual09_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,9,11]
def points : Finset C13.Point := {2,6,9,11}
def columns : List Code := [254,379,439,443,445,446,475,491,506,631,699,758,829,830,923,939,953,954,956,971,979,995,1010,1211,1262,1339,1371,1387,1402,1435,1447,1451,1453,1454,1459,1461,1462,1465,1466,1468,1483,1498,1514,1639,1646,1654,1691,1707,1721,1722,1766,1838,1852,1894,1931,1945,1962,1976,1987,2018,2235,2269,2300,2363,2411,2425,2455,2462,2475,2483,2486,2490,2537,2552,2647,2653,2677,2731,2746,2773,2804,2901,2986,3056,3131,3243,3251,3258,3277,3278,3292,3308,3371,3379,3433,3470,3478,3498,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 523,1,1⟩,⟨.covers 101,1,2⟩,⟨.covers 773,1,1⟩,⟨.covers 774,1,2⟩,⟨.covers 2566,1,2⟩,⟨.covers 2572,1,2⟩,⟨.covers 2820,1,1⟩,⟨.covers 3588,1,2⟩,⟨.covers 2824,1,2⟩,⟨.covers 3592,1,2⟩,⟨.covers 1584,1,1⟩,⟨.covers 1808,1,1⟩,⟨.covers 1728,1,2⟩,⟨.covers 2752,1,2⟩,⟨.incident 9,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_011
namespace C13.Global.FastDual09_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,8,9]
def points : Finset C13.Point := {2,7,8,9}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,892,971,979,995,1147,1261,1371,1387,1401,1402,1447,1453,1461,1509,1639,1646,1653,1654,1660,1691,1707,1721,1739,1753,1852,1987,2171,2270,2395,2411,2425,2426,2455,2462,2486,2518,2647,2653,2677,2678,2684,2715,2731,2746,2763,2794,2876,3011,3131,3163,3179,3187,3193,3194,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 1031,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 267,1,4⟩,⟨.covers 141,1,1⟩,⟨.covers 269,1,7⟩,⟨.covers 2061,1,3⟩,⟨.covers 149,1,1⟩,⟨.covers 2069,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 2309,1,12⟩,⟨.covers 169,1,1⟩,⟨.covers 777,1,10⟩,⟨.covers 1289,1,4⟩,⟨.covers 2569,1,4⟩,⟨.covers 1553,1,1⟩,⟨.covers 2577,1,1⟩,⟨.covers 2145,1,3⟩,⟨.covers 2337,1,1⟩,⟨.covers 1038,1,5⟩,⟨.covers 166,1,12⟩,⟨.covers 774,1,17⟩,⟨.covers 2566,1,3⟩,⟨.covers 1050,1,3⟩,⟨.covers 2314,1,4⟩,⟨.covers 1546,1,2⟩,⟨.covers 178,1,1⟩,⟨.covers 1298,1,1⟩,⟨.covers 1570,1,2⟩,⟨.covers 2594,1,1⟩,⟨.covers 2316,1,9⟩,⟨.covers 212,1,5⟩,⟨.covers 228,1,1⟩,⟨.covers 1796,1,17⟩,⟨.covers 2820,1,7⟩,⟨.covers 184,1,4⟩,⟨.covers 368,1,4⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,6⟩,⟨.covers 912,1,15⟩,⟨.covers 1424,1,13⟩,⟨.covers 2704,1,1⟩,⟨.covers 2272,1,4⟩,⟨.covers 1376,1,4⟩,⟨.covers 2656,1,2⟩,⟨.covers 928,1,15⟩,⟨.covers 2464,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 1472,1,7⟩,⟨.covers 1856,1,8⟩,⟨.covers 2880,1,15⟩,⟨.incident 2,8,-1⟩,⟨.incident 8,8,-9⟩,⟨.incident 9,8,-3⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_012
namespace C13.Global.FastDual09_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,8,11]
def points : Finset C13.Point := {2,7,8,11}
def columns : List Code := [379,439,631,635,637,638,699,731,747,829,830,859,875,889,890,892,971,979,995,1147,1261,1371,1387,1401,1402,1447,1453,1461,1509,1595,1627,1639,1643,1645,1646,1651,1653,1654,1657,1658,1660,1691,1707,1721,1739,1753,1769,1837,1852,1867,1882,1897,1912,1957,1987,2017,2171,2270,2411,2425,2455,2462,2486,2518,2619,2647,2653,2667,2675,2677,2681,2731,2746,2794,2921,2966,3131,3179,3187,3193,3277,3278,3292,3308,3433,3478,3627,3635,3661,3669,3689,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 2055,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 773,1,1⟩,⟨.covers 1038,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3332,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 1328,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 3712,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_013
namespace C13.Global.FastDual09_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,11]
def points : Finset C13.Point := {2,7,9,11}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1387,1395,1401,1402,1447,1453,1461,1509,1639,1646,1653,1654,1660,1691,1707,1721,1739,1753,1838,1852,1894,1908,1931,1945,1987,2001,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2647,2653,2677,2731,2746,2794,2901,2986,3131,3179,3187,3193,3277,3278,3292,3308,3371,3379,3433,3441,3470,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 1031,1,10⟩,⟨.covers 139,1,5⟩,⟨.covers 267,1,1⟩,⟨.covers 2059,1,2⟩,⟨.covers 1043,1,2⟩,⟨.covers 99,1,1⟩,⟨.covers 141,1,2⟩,⟨.covers 269,1,8⟩,⟨.covers 149,1,10⟩,⟨.covers 777,1,2⟩,⟨.covers 2569,1,4⟩,⟨.covers 3081,1,4⟩,⟨.covers 78,1,3⟩,⟨.covers 526,1,5⟩,⟨.covers 198,1,4⟩,⟨.covers 1094,1,2⟩,⟨.covers 774,1,5⟩,⟨.covers 2566,1,14⟩,⟨.covers 3078,1,3⟩,⟨.covers 330,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 210,1,4⟩,⟨.covers 1106,1,1⟩,⟨.covers 834,1,1⟩,⟨.covers 1346,1,1⟩,⟨.covers 284,1,3⟩,⟨.covers 108,1,2⟩,⟨.covers 2316,1,8⟩,⟨.covers 1548,1,1⟩,⟨.covers 2572,1,10⟩,⟨.covers 116,1,2⟩,⟨.covers 228,1,6⟩,⟨.covers 2820,1,14⟩,⟨.covers 3588,1,14⟩,⟨.covers 1176,1,3⟩,⟨.covers 1560,1,1⟩,⟨.covers 360,1,2⟩,⟨.covers 1800,1,1⟩,⟨.covers 2824,1,11⟩,⟨.covers 3592,1,9⟩,⟨.covers 2160,1,1⟩,⟨.covers 2224,1,6⟩,⟨.covers 2352,1,5⟩,⟨.covers 1584,1,7⟩,⟨.covers 2608,1,5⟩,⟨.covers 720,1,1⟩,⟨.covers 912,1,2⟩,⟨.covers 3216,1,8⟩,⟨.covers 480,1,4⟩,⟨.covers 864,1,4⟩,⟨.covers 3168,1,1⟩,⟨.covers 3232,1,2⟩,⟨.covers 3360,1,1⟩,⟨.covers 2496,1,3⟩,⟨.covers 1728,1,6⟩,⟨.covers 2752,1,11⟩,⟨.covers 1920,1,1⟩,⟨.incident 2,8,-3⟩,⟨.incident 9,8,-3⟩,⟨.incident 11,8,-1⟩]
def bound : Int := 8

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_014
namespace C13.Global.FastDual09_015
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,7,8,9]
def points : Finset C13.Point := {6,7,8,9}
def columns : List Code := [127,191,223,239,319,351,367,379,415,431,439,463,575,607,623,631,671,687,699,719,799,815,829,830,847,911,967,971,979,995,1087,1119,1135,1150,1183,1199,1213,1231,1311,1327,1341,1342,1359,1371,1374,1387,1402,1423,1431,1447,1453,1461,1567,1583,1597,1598,1615,1623,1639,1646,1654,1679,1691,1693,1707,1721,1807,1852,1987,2111,2143,2159,2173,2207,2223,2238,2255,2335,2351,2365,2366,2383,2395,2411,2413,2425,2447,2455,2462,2471,2486,2591,2607,2621,2622,2639,2647,2653,2663,2677,2703,2715,2731,2734,2746,2831,2876,3011,3103,3119,3127,3131,3133,3134,3151,3165,3166,3181,3182,3196,3215,3229,3230,3245,3246,3260,3277,3278,3292,3308,3343,3358,3373,3388,3403,3418,3433,3448,3463,3478,3493,3508,3599,3613,3630,3644,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 1043,1,2⟩,⟨.covers 2067,1,2⟩,⟨.covers 1059,1,2⟩,⟨.covers 2083,1,2⟩,⟨.covers 1037,1,2⟩,⟨.covers 149,1,4⟩,⟨.covers 533,1,1⟩,⟨.covers 101,1,4⟩,⟨.covers 293,1,1⟩,⟨.covers 197,1,12⟩,⟨.covers 581,1,2⟩,⟨.covers 2117,1,3⟩,⟨.covers 389,1,2⟩,⟨.covers 1157,1,3⟩,⟨.covers 2309,1,2⟩,⟨.covers 1541,1,2⟩,⟨.covers 89,1,3⟩,⟨.covers 537,1,2⟩,⟨.covers 169,1,4⟩,⟨.covers 297,1,2⟩,⟨.covers 329,1,1⟩,⟨.covers 2121,1,3⟩,⟨.covers 649,1,1⟩,⟨.covers 1161,1,4⟩,⟨.covers 777,1,3⟩,⟨.covers 1289,1,2⟩,⟨.covers 2569,1,2⟩,⟨.covers 2062,1,1⟩,⟨.covers 86,1,4⟩,⟨.covers 278,1,2⟩,⟨.covers 166,1,4⟩,⟨.covers 550,1,1⟩,⟨.covers 1094,1,3⟩,⟨.covers 2182,1,4⟩,⟨.covers 154,1,4⟩,⟨.covers 282,1,1⟩,⟨.covers 106,1,3⟩,⟨.covers 554,1,2⟩,⟨.covers 330,1,2⟩,⟨.covers 1098,1,3⟩,⟨.covers 650,1,2⟩,⟨.covers 2186,1,3⟩,⟨.covers 114,1,3⟩,⟨.covers 178,1,2⟩,⟨.covers 368,1,3⟩,⟨.covers 624,1,2⟩,⟨.covers 432,1,3⟩,⟨.covers 688,1,3⟩,⟨.covers 464,1,27⟩,⟨.covers 2256,1,27⟩,⟨.covers 2384,1,5⟩,⟨.covers 1616,1,3⟩,⟨.covers 1424,1,5⟩,⟨.covers 2704,1,3⟩,⟨.covers 1808,1,8⟩,⟨.covers 2832,1,8⟩,⟨.covers 480,1,27⟩,⟨.covers 2272,1,27⟩,⟨.covers 1376,1,3⟩,⟨.covers 2656,1,5⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,5⟩,⟨.covers 1472,1,27⟩,⟨.covers 2496,1,27⟩,⟨.covers 3392,1,6⟩,⟨.covers 3648,1,7⟩,⟨.covers 3456,1,7⟩,⟨.covers 3712,1,7⟩,⟨.incident 6,8,-9⟩,⟨.incident 7,8,-10⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_015
