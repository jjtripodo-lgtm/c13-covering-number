import C13Global.DirectDualBenchmark
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source20
namespace C13.Global.FastDual20_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,8,9]
def points : Finset C13.Point := {3,7,8,9}
def columns : List Code := [379,381,382,439,471,487,631,699,829,830,892,967,979,995,1143,1245,1371,1374,1401,1402,1404,1431,1447,1461,1479,1509,1623,1639,1653,1654,1691,1693,1721,1753,1852,1987,2167,2286,2411,2413,2425,2426,2428,2455,2471,2486,2503,2518,2647,2663,2677,2678,2731,2734,2746,2794,2876,3011,3127,3159,3175,3187,3189,3190,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,2⟩,⟨.covers 519,1,2⟩,⟨.covers 75,1,6⟩,⟨.covers 2067,1,3⟩,⟨.covers 2061,1,7⟩,⟨.covers 2069,1,2⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,5⟩,⟨.covers 89,1,6⟩,⟨.covers 169,1,6⟩,⟨.covers 777,1,13⟩,⟨.covers 2569,1,1⟩,⟨.covers 1313,1,2⟩,⟨.covers 2337,1,2⟩,⟨.covers 1793,1,13⟩,⟨.covers 2817,1,12⟩,⟨.covers 3329,1,3⟩,⟨.covers 1038,1,8⟩,⟨.covers 166,1,5⟩,⟨.covers 774,1,10⟩,⟨.covers 1286,1,4⟩,⟨.covers 2566,1,2⟩,⟨.covers 1050,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 778,1,4⟩,⟨.covers 2314,1,4⟩,⟨.covers 1546,1,6⟩,⟨.covers 178,1,1⟩,⟨.covers 1074,1,3⟩,⟨.covers 2322,1,2⟩,⟨.covers 1122,1,2⟩,⟨.covers 156,1,2⟩,⟨.covers 172,1,1⟩,⟨.covers 1548,1,2⟩,⟨.covers 1796,1,12⟩,⟨.covers 2820,1,13⟩,⟨.covers 120,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 624,1,2⟩,⟨.covers 432,1,5⟩,⟨.covers 2256,1,6⟩,⟨.covers 2384,1,6⟩,⟨.covers 1616,1,2⟩,⟨.covers 912,1,13⟩,⟨.covers 1424,1,7⟩,⟨.covers 2704,1,6⟩,⟨.covers 1248,1,6⟩,⟨.covers 864,1,11⟩,⟨.covers 1376,1,6⟩,⟨.covers 2656,1,5⟩,⟨.covers 928,1,2⟩,⟨.covers 1696,1,1⟩,⟨.covers 3360,1,2⟩,⟨.covers 2752,1,2⟩,⟨.incident 8,8,-6⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source20.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source20.rootCodes link20 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual20_000
namespace C13.Global.FastDual20_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,8,11]
def points : Finset C13.Point := {3,7,8,11}
def columns : List Code := [379,381,382,439,471,487,631,699,829,830,889,890,892,919,935,967,979,995,1143,1245,1371,1374,1401,1402,1404,1431,1447,1461,1479,1509,1591,1623,1639,1651,1653,1654,1691,1693,1721,1753,1822,1852,1882,1912,1927,1957,1987,2017,2167,2286,2411,2413,2425,2455,2486,2518,2615,2647,2675,2677,2731,2734,2746,2794,2921,2966,3127,3159,3187,3189,3277,3278,3292,3308,3433,3478,3607,3635,3669,3697,3726,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 135,1,2⟩,⟨.covers 2055,1,2⟩,⟨.covers 1035,1,8⟩,⟨.covers 163,1,5⟩,⟨.covers 1283,1,4⟩,⟨.covers 2563,1,2⟩,⟨.covers 141,1,2⟩,⟨.covers 525,1,5⟩,⟨.covers 2061,1,1⟩,⟨.covers 581,1,2⟩,⟨.covers 773,1,5⟩,⟨.covers 3077,1,5⟩,⟨.covers 2569,1,1⟩,⟨.covers 2817,1,12⟩,⟨.covers 3329,1,13⟩,⟨.covers 78,1,3⟩,⟨.covers 270,1,3⟩,⟨.covers 582,1,3⟩,⟨.covers 1098,1,2⟩,⟨.covers 778,1,8⟩,⟨.covers 2314,1,13⟩,⟨.covers 3082,1,3⟩,⟨.covers 1074,1,2⟩,⟨.covers 226,1,3⟩,⟨.covers 1122,1,3⟩,⟨.covers 706,1,2⟩,⟨.covers 92,1,5⟩,⟨.covers 172,1,2⟩,⟨.covers 556,1,2⟩,⟨.covers 2316,1,12⟩,⟨.covers 2572,1,5⟩,⟨.covers 1188,1,2⟩,⟨.covers 804,1,1⟩,⟨.covers 1316,1,1⟩,⟨.covers 1796,1,2⟩,⟨.covers 2820,1,13⟩,⟨.covers 3332,1,12⟩,⟨.covers 120,1,2⟩,⟨.covers 184,1,2⟩,⟨.covers 2160,1,2⟩,⟨.covers 1200,1,5⟩,⟨.covers 2224,1,1⟩,⟨.covers 1328,1,5⟩,⟨.covers 2352,1,10⟩,⟨.covers 2608,1,5⟩,⟨.covers 720,1,8⟩,⟨.covers 848,1,4⟩,⟨.covers 3152,1,2⟩,⟨.covers 3216,1,1⟩,⟨.covers 480,1,3⟩,⟨.covers 2464,1,2⟩,⟨.covers 3232,1,5⟩,⟨.covers 1824,1,2⟩,⟨.covers 1472,1,8⟩,⟨.covers 2496,1,13⟩,⟨.covers 2752,1,3⟩,⟨.incident 8,8,-5⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source20.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source20.rootCodes link20 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual20_001
namespace C13.Global.FastDual20_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,10]
def points : Finset C13.Point := {3,7,9,10}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1371,1374,1383,1395,1398,1402,1447,1461,1509,1639,1654,1691,1693,1721,1753,1894,1945,2167,2286,2359,2391,2407,2411,2413,2414,2419,2421,2422,2425,2426,2428,2455,2471,2486,2503,2518,2534,2647,2663,2677,2678,2731,2734,2746,2794,2862,2876,2887,2901,2918,2932,2986,3011,3042,3127,3175,3187,3190,3277,3278,3292,3308,3367,3379,3406,3418,3430,3442,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 519,1,7⟩,⟨.covers 1031,1,4⟩,⟨.covers 75,1,4⟩,⟨.covers 1035,1,4⟩,⟨.covers 2059,1,7⟩,⟨.covers 83,1,2⟩,⟨.covers 163,1,4⟩,⟨.covers 269,1,2⟩,⟨.covers 525,1,6⟩,⟨.covers 2061,1,9⟩,⟨.covers 2069,1,2⟩,⟨.covers 773,1,2⟩,⟨.covers 3077,1,2⟩,⟨.covers 2097,1,2⟩,⟨.covers 417,1,1⟩,⟨.covers 449,1,1⟩,⟨.covers 1793,1,11⟩,⟨.covers 2817,1,2⟩,⟨.covers 3329,1,4⟩,⟨.covers 3585,1,11⟩,⟨.covers 1038,1,5⟩,⟨.covers 282,1,1⟩,⟨.covers 778,1,9⟩,⟨.covers 1546,1,7⟩,⟨.covers 3082,1,6⟩,⟨.covers 210,1,7⟩,⟨.covers 92,1,4⟩,⟨.covers 284,1,1⟩,⟨.covers 172,1,11⟩,⟨.covers 1548,1,5⟩,⟨.covers 1796,1,11⟩,⟨.covers 3588,1,11⟩,⟨.covers 120,1,4⟩,⟨.covers 2824,1,1⟩,⟨.covers 624,1,2⟩,⟨.covers 1136,1,4⟩,⟨.covers 432,1,4⟩,⟨.covers 1200,1,3⟩,⟨.covers 2224,1,7⟩,⟨.covers 1328,1,2⟩,⟨.covers 2608,1,4⟩,⟨.covers 720,1,1⟩,⟨.covers 2256,1,4⟩,⟨.covers 1616,1,4⟩,⟨.covers 3152,1,2⟩,⟨.covers 2832,1,4⟩,⟨.covers 3344,1,2⟩,⟨.covers 736,1,4⟩,⟨.covers 1696,1,8⟩,⟨.covers 1472,1,8⟩,⟨.covers 1728,1,6⟩,⟨.covers 2752,1,7⟩,⟨.covers 3456,1,3⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source20.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source20.rootCodes link20 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual20_002
namespace C13.Global.FastDual20_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,11]
def points : Finset C13.Point := {3,7,9,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1367,1371,1373,1374,1383,1395,1397,1398,1401,1402,1404,1431,1447,1461,1479,1493,1509,1623,1639,1653,1654,1691,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2647,2677,2731,2734,2746,2794,2901,2986,3127,3159,3187,3189,3277,3278,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 519,1,5⟩,⟨.covers 1031,1,1⟩,⟨.covers 2055,1,5⟩,⟨.covers 75,1,1⟩,⟨.covers 1035,1,10⟩,⟨.covers 99,1,2⟩,⟨.covers 2307,1,4⟩,⟨.covers 1539,1,1⟩,⟨.covers 2061,1,6⟩,⟨.covers 777,1,11⟩,⟨.covers 2569,1,11⟩,⟨.covers 3081,1,4⟩,⟨.covers 2817,1,11⟩,⟨.covers 3585,1,11⟩,⟨.covers 1038,1,11⟩,⟨.covers 1062,1,2⟩,⟨.covers 774,1,4⟩,⟨.covers 778,1,7⟩,⟨.covers 1074,1,2⟩,⟨.covers 210,1,10⟩,⟨.covers 156,1,11⟩,⟨.covers 108,1,4⟩,⟨.covers 2572,1,11⟩,⟨.covers 120,1,6⟩,⟨.covers 2824,1,3⟩,⟨.covers 3592,1,6⟩,⟨.covers 2160,1,4⟩,⟨.covers 432,1,10⟩,⟨.covers 1200,1,1⟩,⟨.covers 1584,1,6⟩,⟨.covers 720,1,1⟩,⟨.covers 2704,1,11⟩,⟨.covers 480,1,8⟩,⟨.covers 1248,1,2⟩,⟨.covers 3168,1,3⟩,⟨.covers 928,1,1⟩,⟨.covers 1696,1,4⟩,⟨.covers 3232,1,1⟩,⟨.covers 1824,1,5⟩,⟨.covers 3360,1,3⟩,⟨.covers 1728,1,10⟩,⟨.covers 2752,1,11⟩,⟨.covers 3456,1,10⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source20.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source20.rootCodes link20 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual20_003
namespace C13.Global.FastDual20_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [8,9,10,11]
def points : Finset C13.Point := {8,9,10,11}
def columns : List Code := [127,191,223,239,247,251,253,254,319,351,367,379,381,382,415,431,439,445,446,463,471,475,478,487,491,493,499,501,502,505,506,508,575,607,623,631,637,638,671,687,699,701,702,719,727,731,733,743,747,750,755,757,758,761,762,764,799,815,829,830,847,892,911,956,967,971,979,995,1009,1010,1012,1016,1087,1119,1135,1143,1147,1150,1183,1199,1207,1211,1213,1231,1243,1245,1246,1255,1261,1262,1267,1269,1270,1273,1274,1276,1311,1327,1359,1371,1374,1402,1423,1447,1453,1461,1498,1509,1521,1522,1524,1528,1567,1583,1615,1639,1646,1654,1679,1691,1693,1721,1753,1766,1777,1778,1780,1784,1807,2032,2111,2143,2159,2167,2171,2173,2207,2223,2231,2235,2238,2255,2263,2269,2270,2283,2285,2286,2291,2293,2294,2297,2298,2300,2335,2351,2383,2411,2413,2425,2447,2455,2462,2486,2518,2537,2545,2546,2548,2552,2591,2607,2639,2647,2653,2677,2703,2731,2734,2746,2773,2794,2801,2802,2804,2808,2831,3056,3103,3119,3127,3131,3151,3187,3215,3251,3277,3278,3292,3308,3313,3314,3316,3320,3343,3568,3599,3824]
def rows : List LinearRow := [⟨.covers 1553,1,1⟩,⟨.covers 1793,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 1570,1,1⟩,⟨.covers 898,1,1⟩,⟨.covers 2690,1,1⟩,⟨.covers 2628,1,1⟩,⟨.covers 792,1,1⟩,⟨.covers 1808,1,1⟩,⟨.covers 2832,1,1⟩,⟨.covers 3600,1,1⟩,⟨.incident 9,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source20.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source20.rootCodes link20 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual20_004
