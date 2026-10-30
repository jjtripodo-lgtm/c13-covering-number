import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source23
namespace C13.Global.FastDual23_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,9]
def points : Finset C13.Point := {3,6,7,9}
def columns : List Code := [379,439,631,699,829,830,855,871,967,979,995,1335,1371,1374,1402,1431,1447,1461,1623,1639,1654,1691,1693,1721,1821,1852,1863,1894,1945,1987,2359,2411,2413,2425,2455,2471,2486,2647,2663,2677,2731,2734,2746,2862,2876,2887,2901,2986,3011,3127,3277,3278,3292,3308,3351,3367,3379,3381,3382,3403,3405,3406,3417,3418,3420,3433,3434,3436,3448,3463,3477,3478,3493,3494,3508,3532,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 135,1,3⟩,⟨.covers 75,1,1⟩,⟨.covers 1035,1,2⟩,⟨.covers 2059,1,2⟩,⟨.covers 77,1,2⟩,⟨.covers 141,1,9⟩,⟨.covers 149,1,3⟩,⟨.covers 101,1,4⟩,⟨.covers 1061,1,2⟩,⟨.covers 89,1,3⟩,⟨.covers 169,1,2⟩,⟨.covers 201,1,3⟩,⟨.covers 777,1,6⟩,⟨.covers 2569,1,7⟩,⟨.covers 209,1,14⟩,⟨.covers 2577,1,2⟩,⟨.covers 225,1,8⟩,⟨.covers 2145,1,2⟩,⟨.covers 1313,1,2⟩,⟨.covers 78,1,2⟩,⟨.covers 142,1,1⟩,⟨.covers 526,1,6⟩,⟨.covers 86,1,4⟩,⟨.covers 2070,1,2⟩,⟨.covers 166,1,3⟩,⟨.covers 198,1,11⟩,⟨.covers 154,1,10⟩,⟨.covers 106,1,3⟩,⟨.covers 1106,1,2⟩,⟨.covers 2322,1,2⟩,⟨.covers 1570,1,2⟩,⟨.covers 212,1,15⟩,⟨.covers 228,1,15⟩,⟨.covers 120,1,1⟩,⟨.covers 3336,1,2⟩,⟨.covers 2384,1,2⟩,⟨.covers 1616,1,2⟩,⟨.covers 912,1,3⟩,⟨.covers 1424,1,3⟩,⟨.covers 2704,1,2⟩,⟨.covers 2832,1,6⟩,⟨.covers 1376,1,2⟩,⟨.covers 2656,1,2⟩,⟨.covers 928,1,9⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,10⟩,⟨.covers 1824,1,6⟩,⟨.covers 2496,1,9⟩,⟨.covers 1728,1,17⟩,⟨.covers 2752,1,8⟩,⟨.covers 3648,1,6⟩,⟨.covers 3456,1,3⟩,⟨.incident 6,8,-5⟩,⟨.incident 7,8,-6⟩,⟨.incident 9,8,-2⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source23.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source23.rootCodes link23 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual23_000
namespace C13.Global.FastDual23_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,10]
def points : Finset C13.Point := {3,6,7,10}
def columns : List Code := [379,439,631,699,823,827,829,830,855,871,883,919,935,947,967,979,995,1335,1371,1374,1402,1447,1461,1591,1639,1654,1691,1693,1721,1819,1831,1843,1882,1894,1906,1945,1957,1969,2359,2411,2413,2425,2455,2471,2486,2615,2647,2663,2677,2731,2734,2746,2839,2855,2859,2861,2862,2867,2869,2870,2873,2874,2876,2887,2899,2901,2915,2917,2921,2929,2951,2963,2966,2979,2982,2986,2994,3011,3127,3277,3278,3292,3308,3367,3379,3406,3418,3493,3532,3623,3635,3686,3725,3737,3788]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 1031,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 1289,1,1⟩,⟨.covers 209,1,1⟩,⟨.covers 225,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 3344,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 1856,1,1⟩,⟨.covers 2880,1,1⟩,⟨.covers 2944,1,1⟩,⟨.covers 3456,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source23.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source23.rootCodes link23 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual23_001
namespace C13.Global.FastDual23_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,11]
def points : Finset C13.Point := {3,6,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,855,871,883,919,935,947,967,979,995,1335,1371,1374,1402,1431,1447,1461,1591,1623,1639,1654,1691,1693,1721,1815,1819,1821,1822,1831,1843,1845,1846,1849,1850,1852,1863,1875,1878,1882,1891,1894,1906,1927,1939,1941,1945,1955,1957,1969,1987,2359,2411,2413,2425,2455,2486,2615,2647,2677,2731,2734,2746,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3277,3278,3292,3308,3351,3379,3405,3433,3478,3532,3607,3635,3669,3726,3754,3788]
def rows : List LinearRow := [⟨.covers 135,1,5⟩,⟨.covers 2055,1,5⟩,⟨.covers 1035,1,11⟩,⟨.covers 525,1,11⟩,⟨.covers 101,1,8⟩,⟨.covers 201,1,11⟩,⟨.covers 2569,1,11⟩,⟨.covers 209,1,11⟩,⟨.covers 225,1,11⟩,⟨.covers 78,1,3⟩,⟨.covers 270,1,8⟩,⟨.covers 526,1,3⟩,⟨.covers 166,1,3⟩,⟨.covers 198,1,5⟩,⟨.covers 2566,1,5⟩,⟨.covers 106,1,11⟩,⟨.covers 202,1,3⟩,⟨.covers 3330,1,5⟩,⟨.covers 108,1,3⟩,⟨.covers 116,1,3⟩,⟨.covers 180,1,3⟩,⟨.covers 212,1,11⟩,⟨.covers 228,1,8⟩,⟨.covers 1316,1,3⟩,⟨.covers 1572,1,3⟩,⟨.covers 184,1,11⟩,⟨.covers 2384,1,11⟩,⟨.covers 1616,1,5⟩,⟨.covers 1424,1,5⟩,⟨.covers 2464,1,5⟩,⟨.covers 3360,1,5⟩,⟨.covers 3616,1,11⟩,⟨.covers 2496,1,11⟩,⟨.covers 2752,1,11⟩,⟨.covers 1856,1,5⟩,⟨.covers 1920,1,5⟩,⟨.covers 2944,1,5⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source23.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source23.rootCodes link23 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual23_002
namespace C13.Global.FastDual23_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,9,10]
def points : Finset C13.Point := {3,6,9,10}
def columns : List Code := [379,439,631,699,701,702,727,743,829,830,855,871,953,954,956,967,979,995,1207,1246,1335,1371,1374,1402,1447,1459,1461,1498,1639,1654,1691,1693,1721,1766,1894,1945,2231,2285,2359,2411,2413,2425,2455,2471,2483,2485,2486,2537,2647,2663,2677,2731,2734,2745,2746,2748,2759,2773,2862,2876,2887,2901,2986,3000,3011,3025,3127,3239,3251,3253,3277,3278,3292,3308,3367,3379,3406,3418,3493,3505,3532,3544,3686,3737]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 1031,1,5⟩,⟨.covers 2059,1,8⟩,⟨.covers 2563,1,2⟩,⟨.covers 269,1,10⟩,⟨.covers 389,1,2⟩,⟨.covers 201,1,10⟩,⟨.covers 1289,1,13⟩,⟨.covers 209,1,5⟩,⟨.covers 526,1,7⟩,⟨.covers 106,1,2⟩,⟨.covers 202,1,11⟩,⟨.covers 2186,1,2⟩,⟨.covers 778,1,2⟩,⟨.covers 1546,1,16⟩,⟨.covers 2098,1,2⟩,⟨.covers 2194,1,1⟩,⟨.covers 898,1,2⟩,⟨.covers 2690,1,1⟩,⟨.covers 1794,1,10⟩,⟨.covers 3330,1,2⟩,⟨.covers 3586,1,1⟩,⟨.covers 92,1,2⟩,⟨.covers 1292,1,11⟩,⟨.covers 1548,1,16⟩,⟨.covers 2572,1,3⟩,⟨.covers 180,1,1⟩,⟨.covers 788,1,3⟩,⟨.covers 2324,1,1⟩,⟨.covers 2580,1,2⟩,⟨.covers 120,1,8⟩,⟨.covers 184,1,3⟩,⟨.covers 1800,1,4⟩,⟨.covers 3592,1,16⟩,⟨.covers 2160,1,2⟩,⟨.covers 1200,1,2⟩,⟨.covers 1328,1,2⟩,⟨.covers 2608,1,4⟩,⟨.covers 848,1,1⟩,⟨.covers 1616,1,11⟩,⟨.covers 3152,1,11⟩,⟨.covers 1376,1,1⟩,⟨.covers 3168,1,10⟩,⟨.covers 928,1,6⟩,⟨.covers 1696,1,11⟩,⟨.covers 3232,1,3⟩,⟨.covers 3360,1,1⟩,⟨.covers 1472,1,2⟩,⟨.covers 2752,1,1⟩,⟨.covers 2880,1,1⟩,⟨.incident 3,8,-5⟩,⟨.incident 9,8,-3⟩,⟨.incident 10,8,-3⟩]
def bound : Int := 6

theorem column_mask : listMask columns = restrictMask universeMask Source23.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source23.rootCodes link23 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual23_003
namespace C13.Global.FastDual23_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,9,11]
def points : Finset C13.Point := {3,6,9,11}
def columns : List Code := [379,439,631,699,701,702,727,743,829,830,855,871,953,954,956,967,979,995,1207,1246,1335,1371,1374,1402,1431,1447,1459,1461,1462,1498,1623,1639,1654,1691,1693,1721,1722,1724,1735,1766,1821,1852,1863,1894,1945,1976,1987,2018,2231,2285,2359,2411,2413,2425,2455,2483,2486,2537,2647,2677,2731,2734,2746,2773,2901,2986,3127,3223,3251,3254,3277,3278,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 2055,1,4⟩,⟨.covers 1035,1,5⟩,⟨.covers 2059,1,5⟩,⟨.covers 2307,1,4⟩,⟨.covers 1539,1,3⟩,⟨.covers 141,1,1⟩,⟨.covers 525,1,4⟩,⟨.covers 89,1,2⟩,⟨.covers 201,1,11⟩,⟨.covers 1161,1,2⟩,⟨.covers 777,1,3⟩,⟨.covers 2569,1,11⟩,⟨.covers 1073,1,4⟩,⟨.covers 225,1,2⟩,⟨.covers 449,1,1⟩,⟨.covers 270,1,7⟩,⟨.covers 390,1,4⟩,⟨.covers 3078,1,4⟩,⟨.covers 106,1,5⟩,⟨.covers 202,1,7⟩,⟨.covers 3082,1,4⟩,⟨.covers 1794,1,1⟩,⟨.covers 2818,1,17⟩,⟨.covers 3586,1,13⟩,⟨.covers 2316,1,14⟩,⟨.covers 1548,1,3⟩,⟨.covers 2572,1,17⟩,⟨.covers 804,1,3⟩,⟨.covers 1572,1,2⟩,⟨.covers 184,1,2⟩,⟨.covers 1136,1,2⟩,⟨.covers 2160,1,9⟩,⟨.covers 2224,1,4⟩,⟨.covers 2352,1,4⟩,⟨.covers 1584,1,3⟩,⟨.covers 3152,1,11⟩,⟨.covers 912,1,5⟩,⟨.covers 2704,1,11⟩,⟨.covers 3216,1,4⟩,⟨.covers 2832,1,13⟩,⟨.covers 3600,1,3⟩,⟨.covers 736,1,3⟩,⟨.covers 864,1,1⟩,⟨.covers 2656,1,4⟩,⟨.covers 3168,1,14⟩,⟨.covers 1728,1,2⟩,⟨.covers 2752,1,2⟩,⟨.incident 3,8,-4⟩,⟨.incident 9,8,-3⟩,⟨.incident 11,8,-7⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source23.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source23.rootCodes link23 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual23_004
namespace C13.Global.FastDual23_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,10,11]
def points : Finset C13.Point := {3,6,10,11}
def columns : List Code := [379,439,631,695,699,701,702,727,743,823,827,829,830,855,871,883,919,935,947,949,950,953,954,956,967,979,995,1207,1246,1335,1371,1374,1402,1447,1459,1461,1498,1591,1639,1654,1691,1693,1703,1715,1717,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2231,2285,2359,2411,2413,2425,2455,2483,2486,2537,2615,2647,2677,2711,2731,2734,2739,2742,2746,2773,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3251,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 209,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 3152,1,1⟩,⟨.covers 736,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 2880,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source23.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source23.rootCodes link23 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual23_005
namespace C13.Global.FastDual23_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,10]
def points : Finset C13.Point := {3,7,9,10}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1371,1374,1383,1395,1398,1402,1447,1461,1509,1639,1654,1691,1693,1721,1753,1894,1945,2167,2286,2359,2391,2407,2411,2413,2414,2419,2421,2422,2425,2426,2428,2455,2471,2486,2503,2518,2534,2647,2663,2677,2678,2731,2734,2746,2794,2862,2876,2887,2901,2918,2932,2986,3011,3042,3127,3175,3187,3190,3277,3278,3292,3308,3367,3379,3406,3418,3430,3442,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 135,1,3⟩,⟨.covers 519,1,6⟩,⟨.covers 1031,1,6⟩,⟨.covers 2055,1,2⟩,⟨.covers 1035,1,9⟩,⟨.covers 2059,1,11⟩,⟨.covers 1283,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 2061,1,11⟩,⟨.covers 2069,1,2⟩,⟨.covers 777,1,9⟩,⟨.covers 113,1,3⟩,⟨.covers 177,1,6⟩,⟨.covers 2129,1,1⟩,⟨.covers 225,1,7⟩,⟨.covers 1313,1,1⟩,⟨.covers 3105,1,1⟩,⟨.covers 833,1,2⟩,⟨.covers 526,1,9⟩,⟨.covers 1038,1,7⟩,⟨.covers 282,1,1⟩,⟨.covers 202,1,2⟩,⟨.covers 1546,1,2⟩,⟨.covers 3082,1,2⟩,⟨.covers 1794,1,11⟩,⟨.covers 3586,1,11⟩,⟨.covers 284,1,1⟩,⟨.covers 1292,1,2⟩,⟨.covers 1548,1,10⟩,⟨.covers 2572,1,2⟩,⟨.covers 180,1,2⟩,⟨.covers 212,1,7⟩,⟨.covers 120,1,7⟩,⟨.covers 232,1,9⟩,⟨.covers 3592,1,11⟩,⟨.covers 624,1,3⟩,⟨.covers 1136,1,3⟩,⟨.covers 2224,1,9⟩,⟨.covers 1584,1,5⟩,⟨.covers 2608,1,2⟩,⟨.covers 720,1,9⟩,⟨.covers 2256,1,4⟩,⟨.covers 1424,1,2⟩,⟨.covers 2832,1,6⟩,⟨.covers 3344,1,8⟩,⟨.covers 1248,1,2⟩,⟨.covers 928,1,2⟩,⟨.covers 1728,1,2⟩,⟨.covers 2944,1,9⟩,⟨.covers 3456,1,9⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source23.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source23.rootCodes link23 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual23_006
namespace C13.Global.FastDual23_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,11]
def points : Finset C13.Point := {3,7,9,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1367,1371,1373,1374,1383,1395,1397,1398,1401,1402,1404,1431,1447,1461,1479,1493,1509,1623,1639,1653,1654,1691,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2647,2677,2731,2734,2746,2794,2901,2986,3127,3159,3187,3189,3277,3278,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 519,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 225,1,1⟩,⟨.covers 1038,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 2832,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2752,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source23.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source23.rootCodes link23 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual23_007
