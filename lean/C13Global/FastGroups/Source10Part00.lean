import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source10
namespace C13.Global.FastDual10_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,9]
def points : Finset C13.Point := {3,6,7,9}
def columns : List Code := [379,439,631,699,829,830,855,871,967,979,995,1335,1371,1374,1402,1431,1447,1461,1623,1639,1654,1691,1693,1721,1821,1852,1863,1894,1945,1987,2359,2411,2413,2425,2455,2471,2486,2647,2663,2677,2731,2734,2746,2862,2876,2887,2901,2986,3011,3127,3277,3278,3292,3308,3351,3367,3379,3381,3382,3403,3405,3406,3417,3418,3420,3433,3434,3436,3448,3463,3477,3478,3493,3494,3508,3532,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 135,1,3⟩,⟨.covers 75,1,1⟩,⟨.covers 1035,1,2⟩,⟨.covers 2059,1,2⟩,⟨.covers 77,1,2⟩,⟨.covers 149,1,3⟩,⟨.covers 101,1,4⟩,⟨.covers 1061,1,2⟩,⟨.covers 89,1,3⟩,⟨.covers 169,1,2⟩,⟨.covers 201,1,12⟩,⟨.covers 777,1,6⟩,⟨.covers 2569,1,7⟩,⟨.covers 209,1,14⟩,⟨.covers 2577,1,2⟩,⟨.covers 225,1,17⟩,⟨.covers 2145,1,2⟩,⟨.covers 1313,1,2⟩,⟨.covers 78,1,2⟩,⟨.covers 86,1,4⟩,⟨.covers 2070,1,2⟩,⟨.covers 166,1,3⟩,⟨.covers 198,1,11⟩,⟨.covers 154,1,10⟩,⟨.covers 106,1,3⟩,⟨.covers 202,1,1⟩,⟨.covers 778,1,6⟩,⟨.covers 1106,1,2⟩,⟨.covers 2322,1,2⟩,⟨.covers 1570,1,2⟩,⟨.covers 156,1,9⟩,⟨.covers 172,1,9⟩,⟨.covers 3588,1,6⟩,⟨.covers 120,1,1⟩,⟨.covers 216,1,6⟩,⟨.covers 232,1,6⟩,⟨.covers 3336,1,2⟩,⟨.covers 2384,1,2⟩,⟨.covers 1616,1,2⟩,⟨.covers 912,1,3⟩,⟨.covers 1424,1,3⟩,⟨.covers 2704,1,2⟩,⟨.covers 2832,1,6⟩,⟨.covers 1376,1,2⟩,⟨.covers 2656,1,2⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,10⟩,⟨.covers 1824,1,6⟩,⟨.covers 2496,1,9⟩,⟨.covers 1728,1,17⟩,⟨.covers 2752,1,5⟩,⟨.covers 2944,1,3⟩,⟨.covers 3456,1,3⟩,⟨.incident 6,8,-5⟩,⟨.incident 7,8,-6⟩,⟨.incident 9,8,-2⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source10.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source10.rootCodes link10 points rows bound = true := by decide +kernel

end C13.Global.FastDual10_000
namespace C13.Global.FastDual10_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,10]
def points : Finset C13.Point := {3,6,7,10}
def columns : List Code := [379,439,631,699,823,827,829,830,855,871,883,919,935,947,967,979,995,1335,1371,1374,1402,1447,1461,1591,1639,1654,1691,1693,1721,1819,1831,1843,1882,1894,1906,1945,1957,1969,2359,2411,2413,2425,2455,2471,2486,2615,2647,2663,2677,2731,2734,2746,2839,2855,2859,2861,2862,2867,2869,2870,2873,2874,2876,2887,2899,2901,2915,2917,2921,2929,2951,2963,2966,2979,2982,2986,2994,3011,3127,3277,3278,3292,3308,3367,3379,3406,3418,3493,3532,3623,3635,3686,3725,3737,3788]
def rows : List LinearRow := [⟨.covers 2059,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 209,1,1⟩,⟨.covers 225,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 3344,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 2880,1,1⟩,⟨.covers 3456,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source10.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source10.rootCodes link10 points rows bound = true := by decide +kernel

end C13.Global.FastDual10_001
namespace C13.Global.FastDual10_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,9,10]
def points : Finset C13.Point := {3,6,9,10}
def columns : List Code := [251,379,439,631,699,701,702,727,743,755,829,830,855,871,953,954,956,967,979,995,1207,1246,1274,1335,1371,1374,1402,1447,1459,1461,1498,1639,1654,1691,1693,1721,1766,1778,1894,1945,2231,2285,2297,2359,2411,2413,2425,2455,2471,2483,2485,2486,2537,2647,2663,2677,2731,2734,2745,2746,2748,2759,2773,2801,2862,2876,2887,2901,2986,3000,3011,3025,3127,3239,3251,3253,3277,3278,3292,3308,3320,3367,3379,3406,3418,3493,3505,3532,3544,3686,3737,3824]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 1031,1,3⟩,⟨.covers 267,1,1⟩,⟨.covers 2059,1,19⟩,⟨.covers 269,1,11⟩,⟨.covers 1037,1,16⟩,⟨.covers 197,1,3⟩,⟨.covers 773,1,1⟩,⟨.covers 1541,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 89,1,3⟩,⟨.covers 1289,1,16⟩,⟨.covers 526,1,8⟩,⟨.covers 778,1,4⟩,⟨.covers 1546,1,20⟩,⟨.covers 3082,1,20⟩,⟨.covers 2194,1,7⟩,⟨.covers 2690,1,1⟩,⟨.covers 92,1,20⟩,⟨.covers 108,1,9⟩,⟨.covers 172,1,5⟩,⟨.covers 1548,1,3⟩,⟨.covers 2572,1,5⟩,⟨.covers 564,1,3⟩,⟨.covers 596,1,1⟩,⟨.covers 2580,1,3⟩,⟨.covers 1188,1,3⟩,⟨.covers 1796,1,7⟩,⟨.covers 3588,1,7⟩,⟨.covers 120,1,15⟩,⟨.covers 312,1,1⟩,⟨.covers 568,1,4⟩,⟨.covers 232,1,3⟩,⟨.covers 1800,1,4⟩,⟨.covers 2824,1,3⟩,⟨.covers 3592,1,20⟩,⟨.covers 1328,1,4⟩,⟨.covers 1584,1,3⟩,⟨.covers 848,1,1⟩,⟨.covers 928,1,7⟩,⟨.covers 1696,1,4⟩,⟨.covers 3360,1,3⟩,⟨.covers 1472,1,20⟩,⟨.covers 2944,1,5⟩,⟨.incident 3,8,-14⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source10.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source10.rootCodes link10 points rows bound = true := by decide +kernel

end C13.Global.FastDual10_002
namespace C13.Global.FastDual10_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,10,11]
def points : Finset C13.Point := {3,6,10,11}
def columns : List Code := [251,379,439,631,695,699,701,702,727,743,755,823,827,829,830,855,871,883,919,935,947,949,950,953,954,956,967,979,995,1207,1246,1274,1335,1371,1374,1402,1447,1459,1461,1498,1591,1639,1654,1691,1693,1703,1715,1717,1721,1766,1778,1819,1831,1843,1882,1894,1906,1945,1957,1969,2231,2285,2297,2359,2411,2413,2425,2455,2483,2486,2537,2615,2647,2677,2711,2731,2734,2739,2742,2746,2773,2801,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3251,3277,3278,3292,3308,3320,3379,3532,3635,3788,3824]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 2055,1,1⟩,⟨.covers 75,1,2⟩,⟨.covers 525,1,2⟩,⟨.covers 101,1,1⟩,⟨.covers 2569,1,2⟩,⟨.covers 3081,1,2⟩,⟨.covers 705,1,1⟩,⟨.covers 526,1,2⟩,⟨.covers 86,1,1⟩,⟨.covers 1546,1,2⟩,⟨.covers 3082,1,2⟩,⟨.covers 450,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 2196,1,1⟩,⟨.covers 1188,1,1⟩,⟨.covers 3332,1,1⟩,⟨.covers 3588,1,2⟩,⟨.covers 2384,1,2⟩,⟨.covers 1424,1,1⟩,⟨.covers 3344,1,2⟩,⟨.covers 3600,1,2⟩,⟨.covers 1376,1,2⟩,⟨.covers 2464,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 1920,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source10.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source10.rootCodes link10 points rows bound = true := by decide +kernel

end C13.Global.FastDual10_003
namespace C13.Global.FastDual10_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,10]
def points : Finset C13.Point := {3,7,9,10}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1371,1374,1383,1395,1398,1402,1447,1461,1509,1639,1654,1691,1693,1721,1753,1894,1945,2167,2286,2359,2391,2407,2411,2413,2414,2419,2421,2422,2425,2426,2428,2455,2471,2486,2503,2518,2534,2647,2663,2677,2678,2731,2734,2746,2794,2862,2876,2887,2901,2918,2932,2986,3011,3042,3127,3175,3187,3190,3277,3278,3292,3308,3367,3379,3406,3418,3430,3442,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 135,1,3⟩,⟨.covers 519,1,5⟩,⟨.covers 1031,1,6⟩,⟨.covers 2055,1,3⟩,⟨.covers 75,1,1⟩,⟨.covers 1035,1,7⟩,⟨.covers 2059,1,10⟩,⟨.covers 83,1,3⟩,⟨.covers 163,1,1⟩,⟨.covers 525,1,9⟩,⟨.covers 2061,1,11⟩,⟨.covers 773,1,1⟩,⟨.covers 113,1,1⟩,⟨.covers 2097,1,3⟩,⟨.covers 225,1,7⟩,⟨.covers 1313,1,2⟩,⟨.covers 833,1,1⟩,⟨.covers 526,1,9⟩,⟨.covers 1038,1,4⟩,⟨.covers 282,1,1⟩,⟨.covers 202,1,2⟩,⟨.covers 1546,1,4⟩,⟨.covers 3082,1,5⟩,⟨.covers 178,1,7⟩,⟨.covers 210,1,5⟩,⟨.covers 92,1,3⟩,⟨.covers 284,1,1⟩,⟨.covers 1292,1,2⟩,⟨.covers 1548,1,2⟩,⟨.covers 2572,1,2⟩,⟨.covers 1796,1,11⟩,⟨.covers 3588,1,11⟩,⟨.covers 120,1,5⟩,⟨.covers 232,1,9⟩,⟨.covers 1800,1,5⟩,⟨.covers 3592,1,11⟩,⟨.covers 624,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 2224,1,4⟩,⟨.covers 1328,1,4⟩,⟨.covers 1584,1,8⟩,⟨.covers 720,1,1⟩,⟨.covers 2256,1,6⟩,⟨.covers 3152,1,2⟩,⟨.covers 1424,1,6⟩,⟨.covers 2832,1,8⟩,⟨.covers 3344,1,3⟩,⟨.covers 1248,1,2⟩,⟨.covers 928,1,1⟩,⟨.covers 1696,1,3⟩,⟨.covers 1728,1,10⟩,⟨.covers 2944,1,10⟩,⟨.covers 3456,1,9⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source10.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source10.rootCodes link10 points rows bound = true := by decide +kernel

end C13.Global.FastDual10_004
namespace C13.Global.FastDual10_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,10,11]
def points : Finset C13.Point := {3,7,10,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,823,827,829,830,855,871,883,885,886,889,890,892,919,935,947,967,979,995,1143,1245,1335,1371,1374,1383,1395,1398,1402,1447,1461,1509,1591,1639,1651,1654,1691,1693,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2615,2647,2675,2677,2731,2734,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3187,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 135,1,7⟩,⟨.covers 1031,1,2⟩,⟨.covers 2055,1,2⟩,⟨.covers 75,1,9⟩,⟨.covers 2059,1,2⟩,⟨.covers 269,1,7⟩,⟨.covers 525,1,3⟩,⟨.covers 2061,1,2⟩,⟨.covers 149,1,2⟩,⟨.covers 101,1,2⟩,⟨.covers 1541,1,5⟩,⟨.covers 3077,1,7⟩,⟨.covers 1289,1,2⟩,⟨.covers 2569,1,9⟩,⟨.covers 3081,1,2⟩,⟨.covers 270,1,7⟩,⟨.covers 526,1,3⟩,⟨.covers 86,1,2⟩,⟨.covers 166,1,2⟩,⟨.covers 2566,1,5⟩,⟨.covers 154,1,10⟩,⟨.covers 3082,1,10⟩,⟨.covers 1292,1,2⟩,⟨.covers 596,1,2⟩,⟨.covers 612,1,2⟩,⟨.covers 1796,1,3⟩,⟨.covers 2820,1,3⟩,⟨.covers 3332,1,3⟩,⟨.covers 3588,1,10⟩,⟨.covers 120,1,2⟩,⟨.covers 1800,1,9⟩,⟨.covers 1136,1,5⟩,⟨.covers 2160,1,5⟩,⟨.covers 1200,1,9⟩,⟨.covers 720,1,10⟩,⟨.covers 2384,1,3⟩,⟨.covers 3216,1,10⟩,⟨.covers 3344,1,10⟩,⟨.covers 3600,1,10⟩,⟨.covers 736,1,10⟩,⟨.covers 1248,1,5⟩,⟨.covers 1376,1,3⟩,⟨.covers 2464,1,9⟩,⟨.covers 1696,1,2⟩,⟨.covers 3232,1,5⟩,⟨.covers 2496,1,5⟩,⟨.covers 1856,1,2⟩,⟨.covers 2880,1,2⟩,⟨.covers 2944,1,2⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source10.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source10.rootCodes link10 points rows bound = true := by decide +kernel

end C13.Global.FastDual10_005
namespace C13.Global.FastDual10_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,7,10,11]
def points : Finset C13.Point := {6,7,10,11}
def columns : List Code := [127,191,223,239,319,351,367,379,415,431,439,463,575,607,623,631,671,687,699,719,799,815,823,827,829,830,847,855,859,871,875,883,911,919,923,935,939,947,967,971,979,995,1087,1119,1135,1150,1183,1199,1213,1231,1311,1327,1335,1339,1359,1371,1374,1390,1402,1423,1437,1447,1453,1461,1567,1583,1591,1595,1615,1630,1639,1646,1654,1679,1691,1693,1709,1721,1807,1819,1831,1843,1870,1882,1894,1906,1933,1945,1957,1969,2111,2143,2159,2173,2207,2223,2238,2255,2335,2351,2359,2363,2383,2397,2411,2413,2425,2447,2455,2462,2478,2486,2591,2607,2615,2619,2639,2647,2653,2669,2677,2703,2718,2731,2734,2746,2831,2839,2859,2867,2893,2901,2921,2929,2958,2966,2986,2994,3103,3119,3127,3131,3151,3215,3277,3278,3292,3308,3343,3379,3532,3599,3635,3788]
def rows : List LinearRow := [⟨.covers 519,1,3⟩,⟨.covers 267,1,4⟩,⟨.covers 523,1,2⟩,⟨.covers 149,1,6⟩,⟨.covers 2069,1,2⟩,⟨.covers 101,1,6⟩,⟨.covers 1061,1,2⟩,⟨.covers 197,1,2⟩,⟨.covers 581,1,2⟩,⟨.covers 2117,1,2⟩,⟨.covers 389,1,1⟩,⟨.covers 1157,1,2⟩,⟨.covers 3077,1,10⟩,⟨.covers 169,1,1⟩,⟨.covers 329,1,1⟩,⟨.covers 649,1,2⟩,⟨.covers 3081,1,5⟩,⟨.covers 177,1,1⟩,⟨.covers 86,1,6⟩,⟨.covers 2070,1,2⟩,⟨.covers 166,1,5⟩,⟨.covers 1062,1,2⟩,⟨.covers 582,1,1⟩,⟨.covers 1094,1,2⟩,⟨.covers 390,1,3⟩,⟨.covers 2182,1,2⟩,⟨.covers 202,1,6⟩,⟨.covers 330,1,3⟩,⟨.covers 650,1,1⟩,⟨.covers 284,1,5⟩,⟨.covers 540,1,5⟩,⟨.covers 300,1,5⟩,⟨.covers 556,1,5⟩,⟨.covers 1796,1,3⟩,⟨.covers 120,1,7⟩,⟨.covers 184,1,6⟩,⟨.covers 1800,1,7⟩,⟨.covers 2824,1,10⟩,⟨.covers 1136,1,2⟩,⟨.covers 2160,1,2⟩,⟨.covers 1200,1,2⟩,⟨.covers 2224,1,2⟩,⟨.covers 720,1,19⟩,⟨.covers 1232,1,19⟩,⟨.covers 2384,1,9⟩,⟨.covers 1616,1,6⟩,⟨.covers 1424,1,6⟩,⟨.covers 2704,1,9⟩,⟨.covers 3344,1,19⟩,⟨.covers 3600,1,19⟩,⟨.covers 736,1,19⟩,⟨.covers 1248,1,19⟩,⟨.covers 1376,1,7⟩,⟨.covers 2656,1,4⟩,⟨.covers 2464,1,4⟩,⟨.covers 1696,1,7⟩,⟨.covers 1472,1,19⟩,⟨.covers 1728,1,19⟩,⟨.covers 1856,1,4⟩,⟨.covers 2880,1,4⟩,⟨.covers 1920,1,4⟩,⟨.covers 2944,1,4⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source10.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source10.rootCodes link10 points rows bound = true := by decide +kernel

end C13.Global.FastDual10_006
namespace C13.Global.FastDual10_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,9,10,11]
def points : Finset C13.Point := {6,9,10,11}
def columns : List Code := [127,191,223,239,251,319,351,367,379,415,431,439,443,445,446,463,475,491,575,607,623,631,671,687,699,701,702,719,727,743,755,799,815,829,830,847,855,871,911,923,925,939,942,953,954,956,967,971,979,995,1087,1119,1135,1150,1183,1199,1207,1211,1213,1231,1246,1262,1274,1311,1327,1335,1339,1359,1371,1374,1390,1402,1423,1435,1437,1447,1453,1459,1461,1465,1486,1498,1567,1583,1615,1639,1646,1654,1679,1691,1693,1721,1766,1778,1807,1894,1945,2111,2143,2159,2173,2207,2223,2231,2235,2238,2255,2269,2285,2297,2335,2351,2359,2363,2383,2397,2411,2413,2425,2447,2455,2462,2475,2478,2483,2486,2490,2509,2537,2591,2607,2639,2647,2653,2677,2703,2731,2734,2746,2773,2801,2831,2901,2986,3103,3119,3127,3131,3151,3215,3251,3277,3278,3292,3308,3320,3343,3379,3532,3599,3824]
def rows : List LinearRow := [⟨.covers 71,1,9⟩,⟨.covers 263,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,3⟩,⟨.covers 267,1,24⟩,⟨.covers 643,1,14⟩,⟨.covers 77,1,6⟩,⟨.covers 141,1,1⟩,⟨.covers 269,1,3⟩,⟨.covers 149,1,4⟩,⟨.covers 101,1,4⟩,⟨.covers 1061,1,18⟩,⟨.covers 197,1,9⟩,⟨.covers 1157,1,16⟩,⟨.covers 2089,1,17⟩,⟨.covers 113,1,10⟩,⟨.covers 177,1,1⟩,⟨.covers 209,1,11⟩,⟨.covers 353,1,12⟩,⟨.covers 417,1,5⟩,⟨.covers 1185,1,17⟩,⟨.covers 449,1,9⟩,⟨.covers 705,1,1⟩,⟨.covers 78,1,6⟩,⟨.covers 142,1,1⟩,⟨.covers 270,1,3⟩,⟨.covers 86,1,4⟩,⟨.covers 2070,1,18⟩,⟨.covers 166,1,4⟩,⟨.covers 198,1,9⟩,⟨.covers 2182,1,16⟩,⟨.covers 1050,1,17⟩,⟨.covers 114,1,10⟩,⟨.covers 178,1,1⟩,⟨.covers 338,1,12⟩,⟨.covers 402,1,5⟩,⟨.covers 2194,1,17⟩,⟨.covers 226,1,11⟩,⟨.covers 450,1,9⟩,⟨.covers 706,1,1⟩,⟨.covers 92,1,13⟩,⟨.covers 156,1,1⟩,⟨.covers 540,1,12⟩,⟨.covers 108,1,13⟩,⟨.covers 172,1,1⟩,⟨.covers 556,1,12⟩,⟨.covers 564,1,16⟩,⟨.covers 2196,1,6⟩,⟨.covers 1188,1,6⟩,⟨.covers 3588,1,4⟩,⟨.covers 312,1,6⟩,⟨.covers 568,1,17⟩,⟨.covers 216,1,11⟩,⟨.covers 344,1,8⟩,⟨.covers 232,1,11⟩,⟨.covers 360,1,8⟩,⟨.covers 2824,1,4⟩,⟨.covers 2384,1,1⟩,⟨.covers 1808,1,35⟩,⟨.covers 2832,1,30⟩,⟨.covers 3344,1,36⟩,⟨.covers 1824,1,31⟩,⟨.covers 2848,1,31⟩,⟨.covers 3392,1,32⟩,⟨.incident 6,8,4⟩,⟨.incident 9,8,32⟩,⟨.incident 10,8,31⟩,⟨.incident 11,8,31⟩]
def bound : Int := 99

theorem column_mask : listMask columns = restrictMask universeMask Source10.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source10.rootCodes link10 points rows bound = true := by decide +kernel

end C13.Global.FastDual10_007
