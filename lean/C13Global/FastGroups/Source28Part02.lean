import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source28
namespace C13.Global.FastDual28_016
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,10]
def points : Finset C13.Point := {2,7,9,10}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1639,1646,1654,1691,1721,1753,1894,1945,2171,2270,2363,2395,2411,2419,2425,2426,2455,2462,2486,2518,2647,2653,2677,2678,2684,2715,2731,2746,2763,2794,2845,2876,2901,2932,2955,2986,3011,3042,3131,3163,3187,3194,3277,3278,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 135,1,2⟩,⟨.covers 2055,1,3⟩,⟨.covers 1035,1,5⟩,⟨.covers 163,1,2⟩,⟨.covers 643,1,1⟩,⟨.covers 1283,1,5⟩,⟨.covers 2563,1,3⟩,⟨.covers 77,1,1⟩,⟨.covers 525,1,5⟩,⟨.covers 293,1,1⟩,⟨.covers 197,1,11⟩,⟨.covers 2117,1,1⟩,⟨.covers 1541,1,16⟩,⟨.covers 3077,1,1⟩,⟨.covers 2097,1,5⟩,⟨.covers 270,1,5⟩,⟨.covers 1038,1,9⟩,⟨.covers 1286,1,5⟩,⟨.covers 330,1,5⟩,⟨.covers 778,1,1⟩,⟨.covers 3082,1,5⟩,⟨.covers 226,1,2⟩,⟨.covers 1794,1,11⟩,⟨.covers 3586,1,16⟩,⟨.covers 1292,1,13⟩,⟨.covers 1548,1,7⟩,⟨.covers 212,1,5⟩,⟨.covers 228,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 808,1,1⟩,⟨.covers 2600,1,1⟩,⟨.covers 1800,1,12⟩,⟨.covers 2824,1,2⟩,⟨.covers 3592,1,16⟩,⟨.covers 1136,1,5⟩,⟨.covers 1200,1,5⟩,⟨.covers 2224,1,5⟩,⟨.covers 1328,1,5⟩,⟨.covers 1584,1,11⟩,⟨.covers 2608,1,1⟩,⟨.covers 848,1,6⟩,⟨.covers 3152,1,5⟩,⟨.covers 1424,1,4⟩,⟨.covers 928,1,2⟩,⟨.covers 3232,1,12⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,16⟩,⟨.covers 2752,1,3⟩,⟨.incident 9,8,-2⟩,⟨.incident 10,8,-9⟩]
def bound : Int := 6

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_016
namespace C13.Global.FastDual28_017
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,11]
def points : Finset C13.Point := {2,7,9,11}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1387,1395,1401,1402,1447,1453,1461,1509,1639,1646,1653,1654,1660,1691,1707,1721,1739,1753,1838,1852,1894,1908,1931,1945,1987,2001,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2647,2653,2677,2731,2746,2794,2901,2986,3131,3179,3187,3193,3277,3278,3292,3308,3371,3379,3433,3441,3470,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 1031,1,3⟩,⟨.covers 2055,1,6⟩,⟨.covers 139,1,2⟩,⟨.covers 2059,1,4⟩,⟨.covers 147,1,1⟩,⟨.covers 163,1,2⟩,⟨.covers 2307,1,4⟩,⟨.covers 1539,1,4⟩,⟨.covers 269,1,5⟩,⟨.covers 149,1,2⟩,⟨.covers 1541,1,2⟩,⟨.covers 3077,1,9⟩,⟨.covers 329,1,4⟩,⟨.covers 777,1,2⟩,⟨.covers 2569,1,8⟩,⟨.covers 3081,1,4⟩,⟨.covers 78,1,1⟩,⟨.covers 526,1,4⟩,⟨.covers 166,1,1⟩,⟨.covers 774,1,3⟩,⟨.covers 2566,1,11⟩,⟨.covers 3078,1,11⟩,⟨.covers 1074,1,4⟩,⟨.covers 450,1,1⟩,⟨.covers 1602,1,2⟩,⟨.covers 2818,1,7⟩,⟨.covers 3586,1,15⟩,⟨.covers 156,1,9⟩,⟨.covers 284,1,3⟩,⟨.covers 2316,1,1⟩,⟨.covers 1548,1,3⟩,⟨.covers 2572,1,9⟩,⟨.covers 116,1,2⟩,⟨.covers 228,1,5⟩,⟨.covers 2820,1,17⟩,⟨.covers 3588,1,6⟩,⟨.covers 216,1,3⟩,⟨.covers 1560,1,2⟩,⟨.covers 2160,1,4⟩,⟨.covers 1200,1,4⟩,⟨.covers 2352,1,4⟩,⟨.covers 1584,1,3⟩,⟨.covers 720,1,3⟩,⟨.covers 912,1,4⟩,⟨.covers 2704,1,15⟩,⟨.covers 3216,1,1⟩,⟨.covers 2272,1,4⟩,⟨.covers 864,1,5⟩,⟨.covers 3168,1,4⟩,⟨.covers 2464,1,8⟩,⟨.covers 2496,1,11⟩,⟨.covers 1728,1,1⟩,⟨.covers 2752,1,11⟩,⟨.covers 1920,1,1⟩,⟨.incident 2,8,-2⟩,⟨.incident 9,8,-4⟩,⟨.incident 11,8,-7⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_017
namespace C13.Global.FastDual28_018
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,10,11]
def points : Finset C13.Point := {2,7,10,11}
def columns : List Code := [379,439,631,635,637,638,699,731,747,823,827,829,830,859,875,883,885,886,889,890,892,923,939,947,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1595,1627,1639,1646,1651,1654,1658,1691,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2619,2647,2653,2667,2675,2677,2681,2731,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3187,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 135,1,3⟩,⟨.covers 2055,1,3⟩,⟨.covers 139,1,3⟩,⟨.covers 1035,1,5⟩,⟨.covers 2059,1,5⟩,⟨.covers 141,1,8⟩,⟨.covers 269,1,3⟩,⟨.covers 525,1,8⟩,⟨.covers 197,1,3⟩,⟨.covers 2309,1,5⟩,⟨.covers 1541,1,8⟩,⟨.covers 329,1,3⟩,⟨.covers 2569,1,3⟩,⟨.covers 270,1,11⟩,⟨.covers 86,1,5⟩,⟨.covers 166,1,5⟩,⟨.covers 1286,1,3⟩,⟨.covers 3078,1,11⟩,⟨.covers 330,1,3⟩,⟨.covers 1546,1,3⟩,⟨.covers 226,1,8⟩,⟨.covers 450,1,3⟩,⟨.covers 3330,1,11⟩,⟨.covers 3586,1,11⟩,⟨.covers 1548,1,8⟩,⟨.covers 116,1,3⟩,⟨.covers 180,1,3⟩,⟨.covers 2820,1,3⟩,⟨.covers 3332,1,11⟩,⟨.covers 3588,1,3⟩,⟨.covers 184,1,8⟩,⟨.covers 1800,1,3⟩,⟨.covers 2824,1,3⟩,⟨.covers 2160,1,5⟩,⟨.covers 2224,1,3⟩,⟨.covers 720,1,8⟩,⟨.covers 2384,1,3⟩,⟨.covers 1616,1,3⟩,⟨.covers 1424,1,8⟩,⟨.covers 3216,1,11⟩,⟨.covers 1376,1,8⟩,⟨.covers 2656,1,3⟩,⟨.covers 3168,1,5⟩,⟨.covers 1696,1,3⟩,⟨.covers 3232,1,5⟩,⟨.covers 2944,1,8⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_018
namespace C13.Global.FastDual28_019
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,10]
def points : Finset C13.Point := {3,7,9,10}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1371,1374,1383,1395,1398,1402,1447,1461,1509,1639,1654,1691,1693,1721,1753,1894,1945,2167,2286,2359,2391,2407,2411,2413,2414,2419,2421,2422,2425,2426,2428,2455,2471,2486,2503,2518,2534,2647,2663,2677,2678,2731,2734,2746,2794,2862,2876,2887,2901,2918,2932,2986,3011,3042,3127,3175,3187,3190,3277,3278,3292,3308,3367,3379,3406,3418,3430,3442,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 75,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 2224,1,1⟩,⟨.covers 1328,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 3456,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_019
namespace C13.Global.FastDual28_020
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,11]
def points : Finset C13.Point := {3,7,9,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1367,1371,1373,1374,1383,1395,1397,1398,1401,1402,1404,1431,1447,1461,1479,1493,1509,1623,1639,1653,1654,1691,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2647,2677,2731,2734,2746,2794,2901,2986,3127,3159,3187,3189,3277,3278,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 1035,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 1038,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 1584,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 1248,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_020
namespace C13.Global.FastDual28_021
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,10,11]
def points : Finset C13.Point := {3,7,10,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,823,827,829,830,855,871,883,885,886,889,890,892,919,935,947,967,979,995,1143,1245,1335,1371,1374,1383,1395,1398,1402,1447,1461,1509,1591,1639,1651,1654,1691,1693,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2615,2647,2675,2677,2731,2734,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3187,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 75,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 736,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 1472,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source28.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source28.rootCodes link28 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual28_021
