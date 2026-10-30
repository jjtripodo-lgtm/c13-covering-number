import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source42
namespace C13.Global.FastDual42_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,8]
def points : Finset C13.Point := {2,3,6,8}
def columns : List Code := [254,379,439,506,631,699,758,829,830,949,950,956,979,995,1010,1371,1402,1447,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1852,1882,1957,1972,1987,2002,2300,2411,2425,2455,2485,2486,2537,2552,2647,2677,2731,2739,2745,2746,2773,2804,2876,2921,2966,2996,3011,3041,3056,3251,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3635,3655,3669,3670,3685,3686,3700,3723,3731,3737,3738,3747,3753,3754,3761,3762,3768,3781,3782,3788,3796,3812]
def rows : List LinearRow := [⟨.covers 139,1,6⟩,⟨.covers 77,1,25⟩,⟨.covers 269,1,6⟩,⟨.covers 89,1,25⟩,⟨.covers 169,1,6⟩,⟨.covers 777,1,19⟩,⟨.covers 2569,1,6⟩,⟨.covers 270,1,6⟩,⟨.covers 1038,1,25⟩,⟨.covers 778,1,19⟩,⟨.covers 2314,1,25⟩,⟨.covers 1546,1,6⟩,⟨.covers 108,1,25⟩,⟨.covers 1292,1,25⟩,⟨.covers 2316,1,6⟩,⟨.covers 2572,1,19⟩,⟨.covers 1176,1,12⟩,⟨.covers 680,1,6⟩,⟨.covers 3592,1,6⟩,⟨.covers 1376,1,25⟩,⟨.incident 3,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source42.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source42.rootCodes link42 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual42_008
namespace C13.Global.FastDual42_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,11]
def points : Finset C13.Point := {2,3,6,11}
def columns : List Code := [254,379,439,506,631,699,758,823,827,829,830,883,947,949,950,953,954,956,979,995,1010,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1946,1955,1957,1958,1969,1970,1972,1976,1987,2002,2018,2300,2411,2425,2455,2483,2486,2537,2552,2647,2677,2731,2739,2746,2773,2804,2839,2859,2867,2901,2921,2929,2966,2986,2994,3056,3251,3277,3278,3292,3308,3379,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796,3854,3862,3882,3890,3916,3924,3944,3952]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 1031,1,8⟩,⟨.covers 2055,1,24⟩,⟨.covers 75,1,1⟩,⟨.covers 267,1,5⟩,⟨.covers 1035,1,8⟩,⟨.covers 2059,1,22⟩,⟨.covers 77,1,15⟩,⟨.covers 269,1,68⟩,⟨.covers 101,1,26⟩,⟨.covers 2309,1,30⟩,⟨.covers 89,1,23⟩,⟨.covers 2569,1,28⟩,⟨.covers 2129,1,5⟩,⟨.covers 657,1,4⟩,⟨.covers 1553,1,4⟩,⟨.covers 3089,1,27⟩,⟨.covers 2145,1,4⟩,⟨.covers 417,1,4⟩,⟨.covers 1313,1,4⟩,⟨.covers 3105,1,25⟩,⟨.covers 449,1,17⟩,⟨.covers 705,1,19⟩,⟨.covers 78,1,15⟩,⟨.covers 270,1,47⟩,⟨.covers 278,1,8⟩,⟨.covers 550,1,3⟩,⟨.covers 282,1,3⟩,⟨.covers 554,1,8⟩,⟨.covers 114,1,17⟩,⟨.covers 2098,1,8⟩,⟨.covers 1106,1,9⟩,⟨.covers 1122,1,9⟩,⟨.covers 834,1,5⟩,⟨.covers 898,1,5⟩,⟨.covers 2434,1,10⟩,⟨.covers 2690,1,10⟩,⟨.covers 2818,1,5⟩,⟨.covers 420,1,32⟩,⟨.covers 1316,1,36⟩,⟨.covers 1412,1,5⟩,⟨.covers 664,1,36⟩,⟨.covers 1560,1,32⟩,⟨.covers 1672,1,1⟩,⟨.covers 464,1,19⟩,⟨.covers 1424,1,8⟩,⟨.covers 2704,1,7⟩,⟨.covers 3216,1,15⟩,⟨.covers 3344,1,26⟩,⟨.covers 736,1,19⟩,⟨.covers 2464,1,7⟩,⟨.covers 1696,1,8⟩,⟨.covers 3232,1,15⟩,⟨.covers 3616,1,26⟩,⟨.covers 1472,1,10⟩,⟨.covers 1728,1,13⟩,⟨.incident 2,8,17⟩,⟨.incident 3,8,21⟩,⟨.incident 6,8,37⟩,⟨.incident 11,8,17⟩]
def bound : Int := 108

theorem column_mask : listMask columns = restrictMask universeMask Source42.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source42.rootCodes link42 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual42_009
namespace C13.Global.FastDual42_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,8,9]
def points : Finset C13.Point := {2,3,8,9}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,829,830,892,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1401,1402,1447,1461,1462,1491,1498,1507,1509,1521,1522,1524,1528,1639,1653,1654,1691,1721,1722,1747,1753,1763,1766,1777,1778,1780,1784,1852,1987,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2425,2426,2455,2485,2486,2515,2518,2531,2537,2545,2546,2548,2552,2647,2677,2678,2731,2745,2746,2771,2773,2787,2794,2801,2802,2804,2808,2876,3011,3056,3187,3251,3271,3275,3277,3278,3283,3285,3286,3289,3290,3292,3299,3301,3302,3305,3306,3308,3313,3314,3316,3320,3403,3418,3433,3448,3463,3478,3493,3508,3523,3538,3553,3568,3655,3669,3686,3700,3723,3737,3754,3768,3779,3793,3810,3824]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 263,1,8⟩,⟨.covers 139,1,6⟩,⟨.covers 267,1,5⟩,⟨.covers 523,1,5⟩,⟨.covers 269,1,22⟩,⟨.covers 1037,1,16⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,4⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,7⟩,⟨.covers 89,1,4⟩,⟨.covers 1289,1,4⟩,⟨.covers 2569,1,6⟩,⟨.covers 2097,1,5⟩,⟨.covers 593,1,2⟩,⟨.covers 657,1,6⟩,⟨.covers 353,1,1⟩,⟨.covers 417,1,3⟩,⟨.covers 1313,1,2⟩,⟨.covers 270,1,22⟩,⟨.covers 1038,1,16⟩,⟨.covers 86,1,3⟩,⟨.covers 166,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 2566,1,5⟩,⟨.covers 154,1,1⟩,⟨.covers 106,1,3⟩,⟨.covers 2314,1,3⟩,⟨.covers 1546,1,2⟩,⟨.covers 1074,1,7⟩,⟨.covers 2098,1,4⟩,⟨.covers 338,1,1⟩,⟨.covers 402,1,3⟩,⟨.covers 610,1,3⟩,⟨.covers 674,1,5⟩,⟨.covers 1794,1,22⟩,⟨.covers 2818,1,22⟩,⟨.covers 108,1,5⟩,⟨.covers 172,1,1⟩,⟨.covers 1292,1,22⟩,⟨.covers 2316,1,22⟩,⟨.covers 596,1,5⟩,⟨.covers 2132,1,2⟩,⟨.covers 1124,1,4⟩,⟨.covers 1188,1,1⟩,⟨.covers 3332,1,3⟩,⟨.covers 3588,1,5⟩,⟨.covers 1112,1,3⟩,⟨.covers 1176,1,2⟩,⟨.covers 360,1,2⟩,⟨.covers 2152,1,2⟩,⟨.covers 2216,1,1⟩,⟨.covers 3336,1,5⟩,⟨.covers 3592,1,3⟩,⟨.covers 2256,1,2⟩,⟨.covers 848,1,10⟩,⟨.covers 1616,1,1⟩,⟨.covers 1424,1,4⟩,⟨.covers 2704,1,5⟩,⟨.covers 3344,1,4⟩,⟨.covers 2272,1,3⟩,⟨.covers 2656,1,1⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,6⟩,⟨.covers 3616,1,5⟩,⟨.incident 9,8,-7⟩]
def bound : Int := 17

theorem column_mask : listMask columns = restrictMask universeMask Source42.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source42.rootCodes link42 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual42_010
namespace C13.Global.FastDual42_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,8,9]
def points : Finset C13.Point := {2,6,8,9}
def columns : List Code := [254,379,439,445,446,475,491,506,631,699,758,829,830,956,971,979,995,1010,1211,1262,1371,1387,1402,1447,1453,1461,1462,1468,1483,1498,1639,1646,1654,1691,1707,1721,1722,1766,1852,1987,2235,2269,2300,2395,2411,2425,2455,2462,2485,2486,2492,2507,2537,2552,2647,2653,2677,2715,2731,2745,2746,2773,2804,2876,3011,3056,3131,3227,3243,3251,3257,3258,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,8⟩,⟨.covers 75,1,3⟩,⟨.covers 523,1,3⟩,⟨.covers 525,1,17⟩,⟨.covers 1037,1,11⟩,⟨.covers 149,1,6⟩,⟨.covers 101,1,20⟩,⟨.covers 197,1,9⟩,⟨.covers 773,1,4⟩,⟨.covers 2309,1,5⟩,⟨.covers 89,1,3⟩,⟨.covers 1289,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 657,1,3⟩,⟨.covers 353,1,1⟩,⟨.covers 417,1,2⟩,⟨.covers 2337,1,3⟩,⟨.covers 1038,1,1⟩,⟨.covers 2062,1,19⟩,⟨.covers 774,1,20⟩,⟨.covers 1286,1,4⟩,⟨.covers 2566,1,20⟩,⟨.covers 2098,1,6⟩,⟨.covers 2322,1,1⟩,⟨.covers 1794,1,7⟩,⟨.covers 2818,1,7⟩,⟨.covers 108,1,2⟩,⟨.covers 1548,1,17⟩,⟨.covers 212,1,2⟩,⟨.covers 228,1,15⟩,⟨.covers 420,1,4⟩,⟨.covers 1188,1,1⟩,⟨.covers 1796,1,3⟩,⟨.covers 2820,1,20⟩,⟨.covers 3332,1,3⟩,⟨.covers 3592,1,3⟩,⟨.covers 1616,1,20⟩,⟨.covers 912,1,4⟩,⟨.covers 1424,1,7⟩,⟨.covers 3344,1,5⟩,⟨.covers 864,1,3⟩,⟨.covers 1376,1,1⟩,⟨.covers 1696,1,3⟩,⟨.incident 2,8,-14⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source42.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source42.rootCodes link42 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual42_011
namespace C13.Global.FastDual42_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,8,11]
def points : Finset C13.Point := {2,6,8,11}
def columns : List Code := [254,379,439,445,446,475,491,506,631,699,758,829,830,859,875,949,950,956,971,979,995,1010,1211,1262,1371,1387,1402,1447,1453,1461,1462,1468,1483,1498,1595,1639,1646,1654,1691,1707,1715,1721,1722,1766,1837,1852,1867,1882,1957,1972,1987,2002,2235,2269,2300,2411,2425,2455,2462,2486,2537,2552,2619,2647,2653,2677,2731,2739,2746,2773,2804,2921,2966,3056,3131,3243,3251,3258,3277,3278,3292,3308,3433,3478,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 83,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 197,1,1⟩,⟨.covers 773,1,1⟩,⟨.covers 2309,1,2⟩,⟨.covers 417,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 2818,1,2⟩,⟨.covers 3330,1,2⟩,⟨.covers 2316,1,1⟩,⟨.covers 2572,1,2⟩,⟨.covers 664,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 1328,1,1⟩,⟨.covers 3152,1,2⟩,⟨.covers 1808,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 3232,1,1⟩,⟨.incident 2,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source42.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source42.rootCodes link42 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual42_012
namespace C13.Global.FastDual42_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,9,11]
def points : Finset C13.Point := {2,6,9,11}
def columns : List Code := [254,379,439,443,445,446,475,491,506,631,699,758,829,830,923,939,953,954,956,971,979,995,1010,1211,1262,1339,1371,1387,1402,1435,1447,1451,1453,1454,1459,1461,1462,1465,1466,1468,1483,1498,1514,1639,1646,1654,1691,1707,1721,1722,1766,1838,1852,1894,1931,1945,1962,1976,1987,2018,2235,2269,2300,2363,2411,2425,2455,2462,2475,2483,2486,2490,2537,2552,2647,2653,2677,2731,2746,2773,2804,2901,2986,3056,3131,3243,3251,3258,3277,3278,3292,3308,3371,3379,3433,3470,3478,3498,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 135,1,10⟩,⟨.covers 523,1,5⟩,⟨.covers 1035,1,3⟩,⟨.covers 2059,1,8⟩,⟨.covers 1043,1,3⟩,⟨.covers 2307,1,5⟩,⟨.covers 269,1,8⟩,⟨.covers 101,1,12⟩,⟨.covers 197,1,11⟩,⟨.covers 169,1,3⟩,⟨.covers 201,1,3⟩,⟨.covers 777,1,5⟩,⟨.covers 2569,1,2⟩,⟨.covers 2097,1,2⟩,⟨.covers 657,1,3⟩,⟨.covers 353,1,2⟩,⟨.covers 526,1,11⟩,⟨.covers 2062,1,14⟩,⟨.covers 774,1,1⟩,⟨.covers 2566,1,18⟩,⟨.covers 210,1,1⟩,⟨.covers 1106,1,5⟩,⟨.covers 2818,1,18⟩,⟨.covers 3586,1,18⟩,⟨.covers 1100,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 2572,1,15⟩,⟨.covers 228,1,9⟩,⟨.covers 2820,1,18⟩,⟨.covers 3588,1,18⟩,⟨.covers 368,1,5⟩,⟨.covers 2160,1,2⟩,⟨.covers 1584,1,7⟩,⟨.covers 464,1,4⟩,⟨.covers 720,1,2⟩,⟨.covers 2256,1,1⟩,⟨.covers 3216,1,10⟩,⟨.covers 1808,1,5⟩,⟨.covers 3344,1,5⟩,⟨.covers 2272,1,2⟩,⟨.covers 1728,1,1⟩,⟨.covers 1856,1,11⟩,⟨.covers 3392,1,13⟩,⟨.incident 9,8,-2⟩,⟨.incident 11,8,-5⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source42.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source42.rootCodes link42 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual42_013
namespace C13.Global.FastDual42_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,8,9,11]
def points : Finset C13.Point := {6,8,9,11}
def columns : List Code := [127,191,223,239,254,319,351,367,379,415,431,439,445,446,463,475,491,506,575,607,623,631,671,687,699,701,702,719,727,743,758,799,815,829,830,847,911,956,967,971,979,995,1010,1087,1119,1135,1150,1183,1199,1207,1211,1213,1214,1231,1246,1262,1311,1327,1341,1342,1359,1371,1374,1387,1402,1423,1431,1438,1447,1453,1461,1462,1468,1483,1498,1567,1583,1597,1598,1615,1623,1639,1646,1654,1679,1691,1693,1707,1710,1721,1722,1724,1735,1766,1807,1852,1987,2111,2143,2159,2173,2207,2223,2231,2235,2238,2255,2269,2285,2300,2335,2351,2383,2411,2413,2425,2447,2455,2462,2486,2537,2552,2591,2607,2639,2647,2653,2677,2703,2731,2734,2746,2773,2804,2831,3056,3103,3119,3127,3131,3151,3165,3181,3215,3223,3230,3243,3246,3251,3254,3258,3277,3278,3292,3308,3343,3433,3478,3599,3669,3754]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 135,1,1⟩,⟨.covers 1031,1,3⟩,⟨.covers 75,1,6⟩,⟨.covers 139,1,1⟩,⟨.covers 1035,1,3⟩,⟨.covers 83,1,13⟩,⟨.covers 147,1,1⟩,⟨.covers 2067,1,12⟩,⟨.covers 99,1,13⟩,⟨.covers 163,1,1⟩,⟨.covers 2083,1,12⟩,⟨.covers 77,1,9⟩,⟨.covers 1037,1,1⟩,⟨.covers 149,1,4⟩,⟨.covers 101,1,4⟩,⟨.covers 293,1,18⟩,⟨.covers 197,1,9⟩,⟨.covers 389,1,16⟩,⟨.covers 89,1,4⟩,⟨.covers 537,1,18⟩,⟨.covers 169,1,4⟩,⟨.covers 201,1,9⟩,⟨.covers 649,1,16⟩,⟨.covers 2097,1,16⟩,⟨.covers 657,1,6⟩,⟨.covers 417,1,6⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,3⟩,⟨.covers 1038,1,24⟩,⟨.covers 550,1,17⟩,⟨.covers 282,1,17⟩,⟨.covers 1074,1,6⟩,⟨.covers 2098,1,17⟩,⟨.covers 210,1,11⟩,⟨.covers 1106,1,8⟩,⟨.covers 226,1,11⟩,⟨.covers 1122,1,8⟩,⟨.covers 2818,1,4⟩,⟨.covers 3586,1,4⟩,⟨.covers 2188,1,14⟩,⟨.covers 116,1,10⟩,⟨.covers 180,1,1⟩,⟨.covers 212,1,11⟩,⟨.covers 1124,1,12⟩,⟨.covers 420,1,17⟩,⟨.covers 1188,1,5⟩,⟨.covers 1220,1,9⟩,⟨.covers 2244,1,1⟩,⟨.covers 1796,1,5⟩,⟨.covers 120,1,10⟩,⟨.covers 184,1,1⟩,⟨.covers 1112,1,12⟩,⟨.covers 664,1,17⟩,⟨.covers 1176,1,5⟩,⟨.covers 232,1,11⟩,⟨.covers 1224,1,9⟩,⟨.covers 2248,1,1⟩,⟨.covers 3336,1,4⟩,⟨.covers 1808,1,31⟩,⟨.covers 3344,1,35⟩,⟨.covers 3600,1,31⟩,⟨.covers 1376,1,1⟩,⟨.covers 3360,1,26⟩,⟨.covers 3616,1,31⟩,⟨.covers 1856,1,32⟩,⟨.incident 6,8,4⟩,⟨.incident 8,8,31⟩,⟨.incident 9,8,31⟩,⟨.incident 11,8,32⟩]
def bound : Int := 99

theorem column_mask : listMask columns = restrictMask universeMask Source42.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source42.rootCodes link42 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual42_014
