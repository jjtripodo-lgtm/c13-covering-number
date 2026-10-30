import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source06
namespace C13.Global.FastDual06_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,8,9]
def points : Finset C13.Point := {3,7,8,9}
def columns : List Code := [379,381,382,439,471,487,631,699,829,830,892,967,979,995,1143,1245,1371,1374,1401,1402,1404,1431,1447,1461,1479,1509,1623,1639,1653,1654,1691,1693,1721,1753,1852,1987,2167,2286,2411,2413,2425,2426,2428,2455,2471,2486,2503,2518,2647,2663,2677,2678,2731,2734,2746,2794,2876,3011,3127,3159,3175,3187,3189,3190,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 519,1,1⟩,⟨.covers 75,1,6⟩,⟨.covers 2067,1,2⟩,⟨.covers 1059,1,1⟩,⟨.covers 2061,1,7⟩,⟨.covers 149,1,3⟩,⟨.covers 2069,1,1⟩,⟨.covers 2309,1,5⟩,⟨.covers 1541,1,3⟩,⟨.covers 89,1,3⟩,⟨.covers 777,1,14⟩,⟨.covers 1289,1,3⟩,⟨.covers 2569,1,7⟩,⟨.covers 2097,1,1⟩,⟨.covers 2129,1,1⟩,⟨.covers 1313,1,2⟩,⟨.covers 2337,1,2⟩,⟨.covers 1793,1,14⟩,⟨.covers 2817,1,14⟩,⟨.covers 1038,1,7⟩,⟨.covers 166,1,3⟩,⟨.covers 1062,1,1⟩,⟨.covers 774,1,12⟩,⟨.covers 1286,1,5⟩,⟨.covers 2566,1,2⟩,⟨.covers 154,1,7⟩,⟨.covers 106,1,3⟩,⟨.covers 778,1,2⟩,⟨.covers 2314,1,3⟩,⟨.covers 1074,1,2⟩,⟨.covers 1298,1,2⟩,⟨.covers 2322,1,2⟩,⟨.covers 1122,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 180,1,6⟩,⟨.covers 120,1,1⟩,⟨.covers 1800,1,14⟩,⟨.covers 2824,1,12⟩,⟨.covers 3336,1,3⟩,⟨.covers 720,1,1⟩,⟨.covers 2256,1,7⟩,⟨.covers 2384,1,5⟩,⟨.covers 1616,1,2⟩,⟨.covers 912,1,12⟩,⟨.covers 1424,1,3⟩,⟨.covers 1248,1,7⟩,⟨.covers 864,1,12⟩,⟨.covers 1376,1,5⟩,⟨.covers 2656,1,3⟩,⟨.covers 928,1,2⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,7⟩,⟨.covers 3456,1,3⟩,⟨.incident 8,8,-7⟩]
def bound : Int := 8

theorem column_mask : listMask columns = restrictMask universeMask Source06.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source06.rootCodes link06 points rows bound = true := by decide +kernel

end C13.Global.FastDual06_000
namespace C13.Global.FastDual06_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,8,10]
def points : Finset C13.Point := {3,7,8,10}
def columns : List Code := [379,381,382,439,471,487,631,699,829,830,889,890,892,919,935,967,979,995,1143,1245,1371,1374,1402,1447,1461,1509,1591,1639,1651,1654,1691,1693,1721,1753,1882,1957,2167,2286,2411,2413,2425,2426,2428,2455,2471,2486,2503,2518,2615,2647,2663,2675,2677,2678,2731,2734,2746,2794,2861,2876,2921,2936,2951,2966,3011,3026,3127,3175,3187,3190,3277,3278,3292,3308,3418,3493,3623,3635,3686,3698,3725,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 135,1,2⟩,⟨.covers 1031,1,4⟩,⟨.covers 139,1,3⟩,⟨.covers 1035,1,5⟩,⟨.covers 2059,1,5⟩,⟨.covers 2067,1,4⟩,⟨.covers 1283,1,7⟩,⟨.covers 2307,1,3⟩,⟨.covers 1539,1,4⟩,⟨.covers 269,1,6⟩,⟨.covers 201,1,12⟩,⟨.covers 777,1,3⟩,⟨.covers 1289,1,1⟩,⟨.covers 833,1,2⟩,⟨.covers 2369,1,2⟩,⟨.covers 2625,1,1⟩,⟨.covers 1793,1,13⟩,⟨.covers 3329,1,10⟩,⟨.covers 526,1,4⟩,⟨.covers 198,1,1⟩,⟨.covers 774,1,4⟩,⟨.covers 3078,1,4⟩,⟨.covers 202,1,2⟩,⟨.covers 3082,1,5⟩,⟨.covers 1794,1,13⟩,⟨.covers 3330,1,9⟩,⟨.covers 108,1,1⟩,⟨.covers 172,1,4⟩,⟨.covers 1292,1,13⟩,⟨.covers 1548,1,12⟩,⟨.covers 2580,1,3⟩,⟨.covers 612,1,4⟩,⟨.covers 120,1,2⟩,⟨.covers 184,1,5⟩,⟨.covers 1136,1,4⟩,⟨.covers 1200,1,3⟩,⟨.covers 2224,1,3⟩,⟨.covers 2352,1,5⟩,⟨.covers 1584,1,4⟩,⟨.covers 464,1,6⟩,⟨.covers 912,1,2⟩,⟨.covers 1424,1,10⟩,⟨.covers 3216,1,12⟩,⟨.covers 736,1,6⟩,⟨.covers 864,1,2⟩,⟨.covers 1376,1,7⟩,⟨.covers 3168,1,4⟩,⟨.covers 3232,1,3⟩,⟨.covers 1472,1,6⟩,⟨.covers 2496,1,2⟩,⟨.incident 8,8,-1⟩,⟨.incident 10,8,-4⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source06.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source06.rootCodes link06 points rows bound = true := by decide +kernel

end C13.Global.FastDual06_001
namespace C13.Global.FastDual06_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,10]
def points : Finset C13.Point := {3,7,9,10}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1371,1374,1383,1395,1398,1402,1447,1461,1509,1639,1654,1691,1693,1721,1753,1894,1945,2167,2286,2359,2391,2407,2411,2413,2414,2419,2421,2422,2425,2426,2428,2455,2471,2486,2503,2518,2534,2647,2663,2677,2678,2731,2734,2746,2794,2862,2876,2887,2901,2918,2932,2986,3011,3042,3127,3175,3187,3190,3277,3278,3292,3308,3367,3379,3406,3418,3430,3442,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 135,1,4⟩,⟨.covers 519,1,3⟩,⟨.covers 1031,1,6⟩,⟨.covers 75,1,3⟩,⟨.covers 1035,1,7⟩,⟨.covers 2059,1,6⟩,⟨.covers 2067,1,1⟩,⟨.covers 1539,1,2⟩,⟨.covers 2563,1,3⟩,⟨.covers 269,1,1⟩,⟨.covers 525,1,9⟩,⟨.covers 2061,1,9⟩,⟨.covers 2069,1,1⟩,⟨.covers 197,1,2⟩,⟨.covers 3077,1,1⟩,⟨.covers 2097,1,2⟩,⟨.covers 2129,1,1⟩,⟨.covers 417,1,2⟩,⟨.covers 449,1,1⟩,⟨.covers 1793,1,12⟩,⟨.covers 2817,1,3⟩,⟨.covers 3329,1,4⟩,⟨.covers 3585,1,12⟩,⟨.covers 142,1,5⟩,⟨.covers 526,1,3⟩,⟨.covers 282,1,1⟩,⟨.covers 778,1,5⟩,⟨.covers 1546,1,2⟩,⟨.covers 3082,1,4⟩,⟨.covers 1794,1,12⟩,⟨.covers 3586,1,12⟩,⟨.covers 92,1,3⟩,⟨.covers 1292,1,7⟩,⟨.covers 1548,1,3⟩,⟨.covers 2572,1,1⟩,⟨.covers 180,1,4⟩,⟨.covers 120,1,5⟩,⟨.covers 232,1,4⟩,⟨.covers 624,1,1⟩,⟨.covers 1136,1,6⟩,⟨.covers 2224,1,6⟩,⟨.covers 2608,1,4⟩,⟨.covers 464,1,3⟩,⟨.covers 720,1,6⟩,⟨.covers 2256,1,6⟩,⟨.covers 1616,1,5⟩,⟨.covers 3152,1,2⟩,⟨.covers 2832,1,4⟩,⟨.covers 3344,1,4⟩,⟨.covers 736,1,5⟩,⟨.covers 1248,1,7⟩,⟨.covers 928,1,2⟩,⟨.covers 1696,1,12⟩,⟨.covers 1728,1,1⟩,⟨.covers 2944,1,3⟩,⟨.covers 3456,1,4⟩,⟨.incident 10,8,-2⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source06.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source06.rootCodes link06 points rows bound = true := by decide +kernel

end C13.Global.FastDual06_002
namespace C13.Global.FastDual06_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,10,11]
def points : Finset C13.Point := {3,7,10,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,823,827,829,830,855,871,883,885,886,889,890,892,919,935,947,967,979,995,1143,1245,1335,1371,1374,1383,1395,1398,1402,1447,1461,1509,1591,1639,1651,1654,1691,1693,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2615,2647,2675,2677,2731,2734,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3187,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 1035,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 464,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 480,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source06.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source06.rootCodes link06 points rows bound = true := by decide +kernel

end C13.Global.FastDual06_003
namespace C13.Global.FastDual06_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [8,9,10,11]
def points : Finset C13.Point := {8,9,10,11}
def columns : List Code := [127,191,223,239,247,251,253,254,319,351,367,379,381,382,415,431,439,445,446,463,471,475,478,487,491,493,499,501,502,505,506,508,575,607,623,631,637,638,671,687,699,701,702,719,727,731,733,743,747,750,755,757,758,761,762,764,799,815,829,830,847,892,911,956,967,971,979,995,1009,1010,1012,1016,1087,1119,1135,1143,1147,1150,1183,1199,1207,1211,1213,1231,1243,1245,1246,1255,1261,1262,1267,1269,1270,1273,1274,1276,1311,1327,1359,1371,1374,1402,1423,1447,1453,1461,1498,1509,1521,1522,1524,1528,1567,1583,1615,1639,1646,1654,1679,1691,1693,1721,1753,1766,1777,1778,1780,1784,1807,2032,2111,2143,2159,2167,2171,2173,2207,2223,2231,2235,2238,2255,2263,2269,2270,2283,2285,2286,2291,2293,2294,2297,2298,2300,2335,2351,2383,2411,2413,2425,2447,2455,2462,2486,2518,2537,2545,2546,2548,2552,2591,2607,2639,2647,2653,2677,2703,2731,2734,2746,2773,2794,2801,2802,2804,2808,2831,3056,3103,3119,3127,3131,3151,3187,3215,3251,3277,3278,3292,3308,3313,3314,3316,3320,3343,3568,3599,3824]
def rows : List LinearRow := [⟨.covers 3105,1,1⟩,⟨.covers 1793,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 1298,1,1⟩,⟨.covers 1316,1,1⟩,⟨.covers 1572,1,1⟩,⟨.covers 3144,1,1⟩,⟨.covers 1672,1,1⟩,⟨.covers 1808,1,1⟩,⟨.covers 3344,1,1⟩,⟨.covers 3600,1,1⟩,⟨.incident 10,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source06.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source06.rootCodes link06 points rows bound = true := by decide +kernel

end C13.Global.FastDual06_004
