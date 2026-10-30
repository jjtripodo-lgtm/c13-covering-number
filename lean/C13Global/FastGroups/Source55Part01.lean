import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source55
namespace C13.Global.FastDual55_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,5,9,11]
def points : Finset C13.Point := {2,5,9,11}
def columns : List Code := [445,475,638,731,829,830,892,923,956,971,979,985,1243,1255,1371,1435,1447,1453,1461,1483,1491,1497,1498,1509,1639,1646,1654,1691,1739,1747,1753,1766,1838,1852,1894,1908,1931,1945,1987,2001,2171,2235,2263,2269,2270,2283,2363,2411,2425,2455,2462,2475,2517,2518,2524,2537,2647,2653,2731,2746,2773,2794,2901,2986,3131,3179,3187,3243,3251,3277,3278,3285,3286,3292,3371,3379,3433,3441,3470,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 523,1,4⟩,⟨.covers 323,1,1⟩,⟨.covers 2307,1,6⟩,⟨.covers 1539,1,4⟩,⟨.covers 1037,1,4⟩,⟨.covers 2309,1,1⟩,⟨.covers 1541,1,8⟩,⟨.covers 57,1,2⟩,⟨.covers 1049,1,3⟩,⟨.covers 777,1,4⟩,⟨.covers 3081,1,3⟩,⟨.covers 2817,1,16⟩,⟨.covers 3585,1,9⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,3⟩,⟨.covers 166,1,3⟩,⟨.covers 390,1,1⟩,⟨.covers 774,1,12⟩,⟨.covers 2566,1,17⟩,⟨.covers 3078,1,2⟩,⟨.covers 3090,1,1⟩,⟨.covers 450,1,3⟩,⟨.covers 156,1,2⟩,⟨.covers 108,1,11⟩,⟨.covers 2316,1,2⟩,⟨.covers 2572,1,17⟩,⟨.covers 228,1,1⟩,⟨.covers 1176,1,1⟩,⟨.covers 360,1,1⟩,⟨.covers 3144,1,2⟩,⟨.covers 2824,1,8⟩,⟨.covers 3592,1,17⟩,⟨.covers 2160,1,5⟩,⟨.covers 1200,1,4⟩,⟨.covers 2352,1,1⟩,⟨.covers 1584,1,12⟩,⟨.covers 2608,1,17⟩,⟨.covers 720,1,4⟩,⟨.covers 912,1,4⟩,⟨.covers 3216,1,3⟩,⟨.covers 3344,1,1⟩,⟨.covers 736,1,4⟩,⟨.covers 2656,1,13⟩,⟨.covers 3168,1,3⟩,⟨.covers 928,1,6⟩,⟨.covers 2464,1,3⟩,⟨.covers 2496,1,5⟩,⟨.covers 1728,1,4⟩,⟨.incident 9,8,-8⟩,⟨.incident 11,8,-5⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source55.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source55.rootCodes link55 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual55_008
namespace C13.Global.FastDual55_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,10]
def points : Finset C13.Point := {2,7,9,10}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1639,1646,1654,1691,1721,1753,1894,1945,2171,2270,2363,2395,2411,2419,2425,2426,2455,2462,2486,2518,2647,2653,2677,2678,2684,2715,2731,2746,2763,2794,2845,2876,2901,2932,2955,2986,3011,3042,3131,3163,3187,3194,3277,3278,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 2055,1,3⟩,⟨.covers 1035,1,5⟩,⟨.covers 163,1,2⟩,⟨.covers 1283,1,5⟩,⟨.covers 1539,1,13⟩,⟨.covers 2563,1,3⟩,⟨.covers 525,1,3⟩,⟨.covers 2061,1,2⟩,⟨.covers 53,1,1⟩,⟨.covers 197,1,12⟩,⟨.covers 773,1,1⟩,⟨.covers 1541,1,5⟩,⟨.covers 2097,1,3⟩,⟨.covers 3105,1,2⟩,⟨.covers 2625,1,1⟩,⟨.covers 1793,1,7⟩,⟨.covers 3585,1,18⟩,⟨.covers 46,1,1⟩,⟨.covers 198,1,3⟩,⟨.covers 1286,1,7⟩,⟨.covers 330,1,3⟩,⟨.covers 778,1,3⟩,⟨.covers 3082,1,5⟩,⟨.covers 226,1,3⟩,⟨.covers 300,1,2⟩,⟨.covers 1292,1,12⟩,⟨.covers 1548,1,16⟩,⟨.covers 2572,1,1⟩,⟨.covers 228,1,2⟩,⟨.covers 1796,1,10⟩,⟨.covers 3588,1,18⟩,⟨.covers 2600,1,2⟩,⟨.covers 1352,1,2⟩,⟨.covers 1136,1,5⟩,⟨.covers 2224,1,3⟩,⟨.covers 1328,1,5⟩,⟨.covers 1584,1,13⟩,⟨.covers 2608,1,2⟩,⟨.covers 1232,1,9⟩,⟨.covers 848,1,4⟩,⟨.covers 3152,1,5⟩,⟨.covers 912,1,2⟩,⟨.covers 1424,1,9⟩,⟨.covers 928,1,1⟩,⟨.covers 1696,1,5⟩,⟨.covers 3232,1,12⟩,⟨.covers 1728,1,8⟩,⟨.covers 2752,1,2⟩,⟨.incident 9,8,-4⟩,⟨.incident 10,8,-11⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source55.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source55.rootCodes link55 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual55_009
namespace C13.Global.FastDual55_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,11]
def points : Finset C13.Point := {2,7,9,11}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1387,1395,1401,1402,1447,1453,1461,1509,1639,1646,1653,1654,1660,1691,1707,1721,1739,1753,1838,1852,1894,1908,1931,1945,1987,2001,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2647,2653,2677,2731,2746,2794,2901,2986,3131,3179,3187,3193,3277,3278,3292,3308,3371,3379,3433,3441,3470,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 1031,1,3⟩,⟨.covers 2059,1,5⟩,⟨.covers 147,1,1⟩,⟨.covers 1043,1,3⟩,⟨.covers 2307,1,5⟩,⟨.covers 1539,1,2⟩,⟨.covers 2563,1,13⟩,⟨.covers 45,1,2⟩,⟨.covers 141,1,1⟩,⟨.covers 2309,1,9⟩,⟨.covers 3077,1,8⟩,⟨.covers 777,1,4⟩,⟨.covers 3081,1,5⟩,⟨.covers 2817,1,9⟩,⟨.covers 3585,1,9⟩,⟨.covers 46,1,3⟩,⟨.covers 54,1,2⟩,⟨.covers 1094,1,2⟩,⟨.covers 774,1,2⟩,⟨.covers 2566,1,5⟩,⟨.covers 3078,1,12⟩,⟨.covers 3090,1,2⟩,⟨.covers 450,1,2⟩,⟨.covers 156,1,14⟩,⟨.covers 1548,1,2⟩,⟨.covers 2572,1,18⟩,⟨.covers 1560,1,1⟩,⟨.covers 360,1,3⟩,⟨.covers 2376,1,2⟩,⟨.covers 2824,1,16⟩,⟨.covers 3592,1,18⟩,⟨.covers 2160,1,5⟩,⟨.covers 1200,1,2⟩,⟨.covers 2224,1,7⟩,⟨.covers 2352,1,5⟩,⟨.covers 1584,1,3⟩,⟨.covers 2608,1,5⟩,⟨.covers 720,1,3⟩,⟨.covers 912,1,1⟩,⟨.covers 2704,1,5⟩,⟨.covers 2272,1,9⟩,⟨.covers 864,1,3⟩,⟨.covers 2656,1,8⟩,⟨.covers 3168,1,5⟩,⟨.covers 928,1,1⟩,⟨.covers 2496,1,12⟩,⟨.covers 1728,1,2⟩,⟨.incident 9,8,-4⟩,⟨.incident 11,8,-11⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source55.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source55.rootCodes link55 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual55_010
namespace C13.Global.FastDual55_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,10,11]
def points : Finset C13.Point := {2,7,10,11}
def columns : List Code := [379,439,631,635,637,638,699,731,747,823,827,829,830,859,875,883,885,886,889,890,892,923,939,947,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1595,1627,1639,1646,1651,1654,1658,1691,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2619,2647,2653,2667,2675,2677,2681,2731,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3187,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,8⟩,⟨.covers 1031,1,3⟩,⟨.covers 2055,1,3⟩,⟨.covers 139,1,3⟩,⟨.covers 1035,1,6⟩,⟨.covers 2059,1,6⟩,⟨.covers 45,1,3⟩,⟨.covers 525,1,6⟩,⟨.covers 149,1,3⟩,⟨.covers 197,1,8⟩,⟨.covers 2309,1,6⟩,⟨.covers 3077,1,3⟩,⟨.covers 329,1,3⟩,⟨.covers 2569,1,3⟩,⟨.covers 3329,1,11⟩,⟨.covers 3585,1,11⟩,⟨.covers 46,1,8⟩,⟨.covers 142,1,6⟩,⟨.covers 166,1,8⟩,⟨.covers 3078,1,6⟩,⟨.covers 330,1,3⟩,⟨.covers 1546,1,3⟩,⟨.covers 210,1,6⟩,⟨.covers 226,1,8⟩,⟨.covers 450,1,3⟩,⟨.covers 300,1,3⟩,⟨.covers 1292,1,6⟩,⟨.covers 2572,1,3⟩,⟨.covers 116,1,3⟩,⟨.covers 1796,1,8⟩,⟨.covers 2820,1,3⟩,⟨.covers 3332,1,6⟩,⟨.covers 3588,1,8⟩,⟨.covers 184,1,8⟩,⟨.covers 1800,1,3⟩,⟨.covers 2824,1,3⟩,⟨.covers 1136,1,6⟩,⟨.covers 2160,1,6⟩,⟨.covers 2224,1,3⟩,⟨.covers 720,1,3⟩,⟨.covers 1232,1,6⟩,⟨.covers 2384,1,3⟩,⟨.covers 1616,1,3⟩,⟨.covers 1424,1,8⟩,⟨.covers 3216,1,6⟩,⟨.covers 1376,1,3⟩,⟨.covers 2656,1,3⟩,⟨.covers 1696,1,3⟩,⟨.covers 3232,1,11⟩,⟨.covers 2944,1,8⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source55.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source55.rootCodes link55 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual55_011
namespace C13.Global.FastDual55_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,10]
def points : Finset C13.Point := {3,7,9,10}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1371,1374,1383,1395,1398,1402,1447,1461,1509,1639,1654,1691,1693,1721,1753,1894,1945,2167,2286,2359,2391,2407,2411,2413,2414,2419,2421,2422,2425,2426,2428,2455,2471,2486,2503,2518,2534,2647,2663,2677,2678,2731,2734,2746,2794,2862,2876,2887,2901,2918,2932,2986,3011,3042,3127,3175,3187,3190,3277,3278,3292,3308,3367,3379,3406,3418,3430,3442,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 519,1,1⟩,⟨.covers 1031,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 197,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 1038,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 624,1,1⟩,⟨.covers 2224,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 2256,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 736,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source55.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source55.rootCodes link55 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual55_012
namespace C13.Global.FastDual55_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,11]
def points : Finset C13.Point := {3,7,9,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1367,1371,1373,1374,1383,1395,1397,1398,1401,1402,1404,1431,1447,1461,1479,1493,1509,1623,1639,1653,1654,1691,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2647,2677,2731,2734,2746,2794,2901,2986,3127,3159,3187,3189,3277,3278,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 1038,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 624,1,1⟩,⟨.covers 1248,1,1⟩,⟨.covers 928,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 3456,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source55.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source55.rootCodes link55 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual55_013
