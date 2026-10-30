import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source08
namespace C13.Global.FastDual08_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,9,10]
def points : Finset C13.Point := {2,6,9,10}
def columns : List Code := [379,439,443,445,446,475,491,631,699,829,830,923,939,953,954,956,971,979,995,1211,1262,1339,1371,1402,1435,1447,1453,1459,1461,1465,1498,1639,1646,1654,1691,1721,1766,1894,1945,2235,2269,2363,2395,2411,2425,2455,2459,2461,2462,2475,2483,2485,2486,2489,2490,2492,2507,2521,2537,2647,2653,2677,2715,2731,2745,2746,2773,2845,2876,2901,2955,2969,2986,3000,3011,3025,3131,3227,3251,3257,3277,3278,3292,3308,3355,3379,3418,3469,3481,3493,3505,3532,3544,3686,3737]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 2055,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 773,1,1⟩,⟨.covers 2062,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 1584,1,1⟩,⟨.covers 2608,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 3392,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source08.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source08.rootCodes link08 points rows bound = true := by decide +kernel

end C13.Global.FastDual08_008
namespace C13.Global.FastDual08_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,9,11]
def points : Finset C13.Point := {2,6,9,11}
def columns : List Code := [379,439,443,445,446,475,491,631,699,829,830,923,939,953,954,956,971,979,995,1211,1262,1339,1371,1387,1402,1435,1447,1451,1453,1454,1459,1461,1462,1465,1466,1468,1483,1498,1514,1639,1646,1654,1691,1707,1721,1722,1766,1838,1852,1894,1931,1945,1962,1976,1987,2018,2235,2269,2363,2411,2425,2455,2462,2475,2483,2486,2490,2537,2647,2653,2677,2731,2746,2773,2901,2986,3131,3243,3251,3258,3277,3278,3292,3308,3371,3379,3433,3470,3478,3498,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 1856,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source08.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source08.rootCodes link08 points rows bound = true := by decide +kernel

end C13.Global.FastDual08_009
namespace C13.Global.FastDual08_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,10,11]
def points : Finset C13.Point := {2,6,10,11}
def columns : List Code := [379,439,443,445,446,475,491,631,699,823,827,829,830,859,875,883,923,939,947,949,950,953,954,956,971,979,995,1211,1262,1339,1371,1402,1435,1447,1453,1459,1461,1465,1498,1595,1639,1646,1654,1691,1715,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2235,2269,2363,2411,2425,2455,2462,2475,2483,2486,2490,2537,2619,2647,2653,2677,2731,2739,2746,2773,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3251,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 135,1,8⟩,⟨.covers 1031,1,2⟩,⟨.covers 2055,1,3⟩,⟨.covers 75,1,8⟩,⟨.covers 139,1,2⟩,⟨.covers 1035,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 269,1,6⟩,⟨.covers 525,1,5⟩,⟨.covers 101,1,6⟩,⟨.covers 3077,1,10⟩,⟨.covers 1289,1,1⟩,⟨.covers 2569,1,6⟩,⟨.covers 270,1,6⟩,⟨.covers 526,1,5⟩,⟨.covers 1286,1,1⟩,⟨.covers 2566,1,6⟩,⟨.covers 3078,1,10⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,6⟩,⟨.covers 1292,1,2⟩,⟨.covers 116,1,2⟩,⟨.covers 180,1,3⟩,⟨.covers 1796,1,8⟩,⟨.covers 2820,1,2⟩,⟨.covers 3588,1,10⟩,⟨.covers 120,1,2⟩,⟨.covers 184,1,2⟩,⟨.covers 664,1,2⟩,⟨.covers 680,1,2⟩,⟨.covers 1800,1,3⟩,⟨.covers 2824,1,3⟩,⟨.covers 1136,1,8⟩,⟨.covers 1200,1,5⟩,⟨.covers 2224,1,5⟩,⟨.covers 720,1,10⟩,⟨.covers 1232,1,8⟩,⟨.covers 2384,1,8⟩,⟨.covers 3152,1,2⟩,⟨.covers 1424,1,2⟩,⟨.covers 3344,1,10⟩,⟨.covers 3600,1,10⟩,⟨.covers 736,1,10⟩,⟨.covers 2656,1,2⟩,⟨.covers 3168,1,10⟩,⟨.covers 2464,1,2⟩,⟨.covers 2496,1,8⟩,⟨.covers 1856,1,2⟩,⟨.covers 1920,1,3⟩,⟨.covers 2944,1,3⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source08.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source08.rootCodes link08 points rows bound = true := by decide +kernel

end C13.Global.FastDual08_010
namespace C13.Global.FastDual08_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,10]
def points : Finset C13.Point := {2,7,9,10}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1639,1646,1654,1691,1721,1753,1894,1945,2171,2270,2363,2395,2411,2419,2425,2426,2455,2462,2486,2518,2647,2653,2677,2678,2684,2715,2731,2746,2763,2794,2845,2876,2901,2932,2955,2986,3011,3042,3131,3163,3187,3194,3277,3278,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 1031,1,8⟩,⟨.covers 2055,1,5⟩,⟨.covers 139,1,4⟩,⟨.covers 1035,1,3⟩,⟨.covers 83,1,3⟩,⟨.covers 163,1,3⟩,⟨.covers 2083,1,2⟩,⟨.covers 525,1,9⟩,⟨.covers 149,1,2⟩,⟨.covers 773,1,1⟩,⟨.covers 1541,1,6⟩,⟨.covers 3077,1,11⟩,⟨.covers 329,1,1⟩,⟨.covers 2097,1,1⟩,⟨.covers 2145,1,1⟩,⟨.covers 833,1,3⟩,⟨.covers 2625,1,2⟩,⟨.covers 270,1,8⟩,⟨.covers 1038,1,6⟩,⟨.covers 330,1,1⟩,⟨.covers 778,1,2⟩,⟨.covers 1546,1,7⟩,⟨.covers 3082,1,5⟩,⟨.covers 226,1,4⟩,⟨.covers 172,1,11⟩,⟨.covers 1548,1,1⟩,⟨.covers 116,1,2⟩,⟨.covers 180,1,3⟩,⟨.covers 212,1,8⟩,⟨.covers 1796,1,14⟩,⟨.covers 3588,1,14⟩,⟨.covers 344,1,2⟩,⟨.covers 808,1,2⟩,⟨.covers 2344,1,2⟩,⟨.covers 2600,1,2⟩,⟨.covers 1800,1,14⟩,⟨.covers 2824,1,2⟩,⟨.covers 3592,1,14⟩,⟨.covers 1136,1,3⟩,⟨.covers 1200,1,1⟩,⟨.covers 2224,1,5⟩,⟨.covers 1328,1,5⟩,⟨.covers 1584,1,9⟩,⟨.covers 2608,1,4⟩,⟨.covers 848,1,5⟩,⟨.covers 3344,1,3⟩,⟨.covers 928,1,1⟩,⟨.covers 1696,1,4⟩,⟨.covers 1472,1,11⟩,⟨.covers 1728,1,14⟩,⟨.covers 2752,1,5⟩,⟨.covers 2944,1,1⟩,⟨.incident 9,8,-3⟩,⟨.incident 10,8,-3⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source08.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source08.rootCodes link08 points rows bound = true := by decide +kernel

end C13.Global.FastDual08_011
namespace C13.Global.FastDual08_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,11]
def points : Finset C13.Point := {2,7,9,11}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1387,1395,1401,1402,1447,1453,1461,1509,1639,1646,1653,1654,1660,1691,1707,1721,1739,1753,1838,1852,1894,1908,1931,1945,1987,2001,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2647,2653,2677,2731,2746,2794,2901,2986,3131,3179,3187,3193,3277,3278,3292,3308,3371,3379,3433,3441,3470,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 135,1,2⟩,⟨.covers 1031,1,5⟩,⟨.covers 139,1,4⟩,⟨.covers 2059,1,3⟩,⟨.covers 147,1,3⟩,⟨.covers 1043,1,2⟩,⟨.covers 99,1,3⟩,⟨.covers 269,1,8⟩,⟨.covers 149,1,3⟩,⟨.covers 329,1,1⟩,⟨.covers 777,1,2⟩,⟨.covers 2569,1,7⟩,⟨.covers 3081,1,5⟩,⟨.covers 526,1,9⟩,⟨.covers 1094,1,2⟩,⟨.covers 774,1,1⟩,⟨.covers 2566,1,14⟩,⟨.covers 3078,1,9⟩,⟨.covers 330,1,1⟩,⟨.covers 1074,1,1⟩,⟨.covers 210,1,2⟩,⟨.covers 1106,1,1⟩,⟨.covers 834,1,3⟩,⟨.covers 156,1,9⟩,⟨.covers 2316,1,2⟩,⟨.covers 2572,1,7⟩,⟨.covers 116,1,2⟩,⟨.covers 228,1,8⟩,⟨.covers 2820,1,14⟩,⟨.covers 3588,1,14⟩,⟨.covers 792,1,2⟩,⟨.covers 1304,1,2⟩,⟨.covers 1560,1,2⟩,⟨.covers 360,1,2⟩,⟨.covers 1800,1,2⟩,⟨.covers 2824,1,8⟩,⟨.covers 3592,1,11⟩,⟨.covers 2160,1,3⟩,⟨.covers 1200,1,5⟩,⟨.covers 2352,1,5⟩,⟨.covers 1584,1,4⟩,⟨.covers 720,1,2⟩,⟨.covers 912,1,1⟩,⟨.covers 2704,1,14⟩,⟨.covers 3216,1,2⟩,⟨.covers 864,1,5⟩,⟨.covers 2464,1,6⟩,⟨.covers 3232,1,3⟩,⟨.covers 3360,1,3⟩,⟨.covers 2496,1,9⟩,⟨.covers 1728,1,7⟩,⟨.covers 2752,1,14⟩,⟨.covers 1920,1,1⟩,⟨.incident 9,8,-3⟩,⟨.incident 11,8,-3⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source08.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source08.rootCodes link08 points rows bound = true := by decide +kernel

end C13.Global.FastDual08_012
namespace C13.Global.FastDual08_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,10,11]
def points : Finset C13.Point := {2,7,10,11}
def columns : List Code := [379,439,631,635,637,638,699,731,747,823,827,829,830,859,875,883,885,886,889,890,892,923,939,947,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1595,1627,1639,1646,1651,1654,1658,1691,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2619,2647,2653,2667,2675,2677,2681,2731,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3187,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 2055,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 1541,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 166,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 3344,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 1920,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source08.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source08.rootCodes link08 points rows bound = true := by decide +kernel

end C13.Global.FastDual08_013
namespace C13.Global.FastDual08_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,7,10,11]
def points : Finset C13.Point := {6,7,10,11}
def columns : List Code := [127,191,223,239,319,351,367,379,415,431,439,463,575,607,623,631,671,687,699,719,799,815,823,827,829,830,847,855,859,871,875,883,911,919,923,935,939,947,967,971,979,995,1087,1119,1135,1150,1183,1199,1213,1231,1311,1327,1335,1339,1359,1371,1374,1390,1402,1423,1437,1447,1453,1461,1567,1583,1591,1595,1615,1630,1639,1646,1654,1679,1691,1693,1709,1721,1807,1819,1831,1843,1870,1882,1894,1906,1933,1945,1957,1969,2111,2143,2159,2173,2207,2223,2238,2255,2335,2351,2359,2363,2383,2397,2411,2413,2425,2447,2455,2462,2478,2486,2591,2607,2615,2619,2639,2647,2653,2669,2677,2703,2718,2731,2734,2746,2831,2839,2859,2867,2893,2901,2921,2929,2958,2966,2986,2994,3103,3119,3127,3131,3151,3215,3277,3278,3292,3308,3343,3379,3532,3599,3635,3788]
def rows : List LinearRow := [⟨.covers 263,1,5⟩,⟨.covers 523,1,5⟩,⟨.covers 149,1,3⟩,⟨.covers 101,1,4⟩,⟨.covers 1061,1,2⟩,⟨.covers 581,1,4⟩,⟨.covers 1157,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 169,1,2⟩,⟨.covers 2089,1,2⟩,⟨.covers 201,1,7⟩,⟨.covers 2121,1,2⟩,⟨.covers 649,1,3⟩,⟨.covers 1161,1,1⟩,⟨.covers 86,1,4⟩,⟨.covers 2070,1,2⟩,⟨.covers 166,1,4⟩,⟨.covers 390,1,4⟩,⟨.covers 2182,1,1⟩,⟨.covers 3078,1,14⟩,⟨.covers 154,1,3⟩,⟨.covers 1050,1,2⟩,⟨.covers 106,1,2⟩,⟨.covers 330,1,4⟩,⟨.covers 1098,1,1⟩,⟨.covers 284,1,5⟩,⟨.covers 540,1,5⟩,⟨.covers 300,1,5⟩,⟨.covers 556,1,5⟩,⟨.covers 116,1,7⟩,⟨.covers 180,1,1⟩,⟨.covers 1796,1,8⟩,⟨.covers 2820,1,1⟩,⟨.covers 184,1,6⟩,⟨.covers 1800,1,2⟩,⟨.covers 2824,1,9⟩,⟨.covers 1136,1,2⟩,⟨.covers 2160,1,2⟩,⟨.covers 1200,1,2⟩,⟨.covers 2224,1,2⟩,⟨.covers 720,1,19⟩,⟨.covers 1232,1,19⟩,⟨.covers 2384,1,11⟩,⟨.covers 1616,1,6⟩,⟨.covers 1424,1,9⟩,⟨.covers 2704,1,8⟩,⟨.covers 3344,1,19⟩,⟨.covers 3600,1,19⟩,⟨.covers 736,1,19⟩,⟨.covers 1248,1,19⟩,⟨.covers 1376,1,7⟩,⟨.covers 2656,1,2⟩,⟨.covers 2464,1,6⟩,⟨.covers 1696,1,4⟩,⟨.covers 1472,1,19⟩,⟨.covers 1728,1,19⟩,⟨.covers 1856,1,4⟩,⟨.covers 2880,1,4⟩,⟨.covers 1920,1,3⟩,⟨.covers 2944,1,4⟩]
def bound : Int := 20

theorem column_mask : listMask columns = restrictMask universeMask Source08.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source08.rootCodes link08 points rows bound = true := by decide +kernel

end C13.Global.FastDual08_014
