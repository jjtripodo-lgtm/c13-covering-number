import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source40
namespace C13.Global.FastDual40_040
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,8,11]
def points : Finset C13.Point := {2,7,8,11}
def columns : List Code := [379,439,631,635,637,638,699,731,747,829,830,859,875,889,890,892,971,979,995,1147,1261,1371,1387,1401,1402,1447,1453,1461,1509,1595,1627,1639,1643,1645,1646,1651,1653,1654,1657,1658,1660,1691,1707,1721,1739,1753,1769,1837,1852,1867,1882,1897,1912,1957,1987,2017,2171,2270,2411,2425,2455,2462,2486,2518,2619,2647,2653,2667,2675,2677,2681,2731,2746,2794,2921,2966,3131,3179,3187,3193,3277,3278,3292,3308,3433,3478,3627,3635,3661,3669,3689,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 1031,1,10⟩,⟨.covers 139,1,1⟩,⟨.covers 267,1,4⟩,⟨.covers 2059,1,5⟩,⟨.covers 1043,1,3⟩,⟨.covers 163,1,1⟩,⟨.covers 2563,1,4⟩,⟨.covers 269,1,9⟩,⟨.covers 2061,1,3⟩,⟨.covers 533,1,1⟩,⟨.covers 197,1,2⟩,⟨.covers 773,1,1⟩,⟨.covers 2309,1,11⟩,⟨.covers 3077,1,6⟩,⟨.covers 270,1,4⟩,⟨.covers 526,1,1⟩,⟨.covers 1038,1,10⟩,⟨.covers 2566,1,5⟩,⟨.covers 1050,1,2⟩,⟨.covers 778,1,6⟩,⟨.covers 2314,1,1⟩,⟨.covers 226,1,9⟩,⟨.covers 1794,1,1⟩,⟨.covers 2818,1,5⟩,⟨.covers 3330,1,11⟩,⟨.covers 3586,1,1⟩,⟨.covers 92,1,7⟩,⟨.covers 156,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 2316,1,4⟩,⟨.covers 116,1,3⟩,⟨.covers 180,1,3⟩,⟨.covers 228,1,8⟩,⟨.covers 3588,1,2⟩,⟨.covers 184,1,9⟩,⟨.covers 1176,1,1⟩,⟨.covers 1304,1,2⟩,⟨.covers 2824,1,11⟩,⟨.covers 3336,1,11⟩,⟨.covers 2160,1,5⟩,⟨.covers 1328,1,8⟩,⟨.covers 2352,1,5⟩,⟨.covers 1584,1,1⟩,⟨.covers 2608,1,2⟩,⟨.covers 720,1,10⟩,⟨.covers 848,1,1⟩,⟨.covers 3152,1,2⟩,⟨.covers 480,1,1⟩,⟨.covers 2272,1,2⟩,⟨.covers 2464,1,2⟩,⟨.covers 2496,1,11⟩,⟨.covers 1920,1,10⟩,⟨.covers 3712,1,9⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_040
namespace C13.Global.FastDual40_041
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,11]
def points : Finset C13.Point := {2,7,9,11}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1387,1395,1401,1402,1447,1453,1461,1509,1639,1646,1653,1654,1660,1691,1707,1721,1739,1753,1838,1852,1894,1908,1931,1945,1987,2001,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2647,2653,2677,2731,2746,2794,2901,2986,3131,3179,3187,3193,3277,3278,3292,3308,3371,3379,3433,3441,3470,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 1031,1,6⟩,⟨.covers 2055,1,8⟩,⟨.covers 139,1,2⟩,⟨.covers 2059,1,4⟩,⟨.covers 1043,1,2⟩,⟨.covers 2307,1,4⟩,⟨.covers 1539,1,2⟩,⟨.covers 269,1,4⟩,⟨.covers 3077,1,6⟩,⟨.covers 201,1,2⟩,⟨.covers 329,1,2⟩,⟨.covers 777,1,2⟩,⟨.covers 2569,1,8⟩,⟨.covers 3081,1,4⟩,⟨.covers 78,1,2⟩,⟨.covers 526,1,4⟩,⟨.covers 774,1,2⟩,⟨.covers 2566,1,6⟩,⟨.covers 3078,1,10⟩,⟨.covers 1074,1,2⟩,⟨.covers 210,1,2⟩,⟨.covers 1346,1,2⟩,⟨.covers 1794,1,2⟩,⟨.covers 2818,1,15⟩,⟨.covers 3586,1,15⟩,⟨.covers 156,1,8⟩,⟨.covers 284,1,2⟩,⟨.covers 108,1,2⟩,⟨.covers 172,1,2⟩,⟨.covers 2316,1,2⟩,⟨.covers 2572,1,6⟩,⟨.covers 180,1,6⟩,⟨.covers 2820,1,15⟩,⟨.covers 3588,1,8⟩,⟨.covers 1176,1,2⟩,⟨.covers 360,1,2⟩,⟨.covers 2160,1,4⟩,⟨.covers 2224,1,2⟩,⟨.covers 2352,1,4⟩,⟨.covers 1584,1,6⟩,⟨.covers 720,1,2⟩,⟨.covers 912,1,4⟩,⟨.covers 2704,1,12⟩,⟨.covers 3216,1,2⟩,⟨.covers 480,1,6⟩,⟨.covers 2272,1,4⟩,⟨.covers 864,1,2⟩,⟨.covers 2656,1,10⟩,⟨.covers 3168,1,4⟩,⟨.covers 2496,1,10⟩,⟨.covers 1728,1,2⟩,⟨.incident 9,8,-2⟩,⟨.incident 11,8,-6⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_041
namespace C13.Global.FastDual40_042
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,8]
def points : Finset C13.Point := {3,6,7,8}
def columns : List Code := [379,439,631,699,829,830,919,935,967,979,995,1371,1374,1402,1431,1447,1461,1591,1623,1639,1654,1691,1693,1721,1822,1852,1882,1927,1957,1987,2411,2413,2425,2455,2471,2486,2615,2647,2663,2677,2731,2734,2746,2861,2876,2921,2951,2966,3011,3127,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3607,3623,3635,3637,3638,3655,3669,3670,3685,3686,3700,3723,3725,3726,3737,3738,3740,3753,3754,3756,3768,3788,3854,3884,3914,3944,3974,4004,4034,4064]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 101,1,6⟩,⟨.covers 201,1,25⟩,⟨.covers 1289,1,25⟩,⟨.covers 2625,1,6⟩,⟨.covers 78,1,6⟩,⟨.covers 86,1,6⟩,⟨.covers 198,1,19⟩,⟨.covers 106,1,25⟩,⟨.covers 210,1,12⟩,⟨.covers 226,1,25⟩,⟨.covers 92,1,12⟩,⟨.covers 116,1,6⟩,⟨.covers 212,1,12⟩,⟨.covers 228,1,25⟩,⟨.covers 1604,1,6⟩,⟨.covers 2628,1,6⟩,⟨.covers 848,1,12⟩,⟨.covers 2384,1,25⟩,⟨.covers 1616,1,6⟩,⟨.covers 1856,1,6⟩,⟨.covers 2880,1,19⟩,⟨.incident 6,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_042
namespace C13.Global.FastDual40_043
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,9]
def points : Finset C13.Point := {3,6,7,9}
def columns : List Code := [379,439,631,699,829,830,855,871,967,979,995,1335,1371,1374,1402,1431,1447,1461,1623,1639,1654,1691,1693,1721,1821,1852,1863,1894,1945,1987,2359,2411,2413,2425,2455,2471,2486,2647,2663,2677,2731,2734,2746,2862,2876,2887,2901,2986,3011,3127,3277,3278,3292,3308,3351,3367,3379,3381,3382,3403,3405,3406,3417,3418,3420,3433,3434,3436,3448,3463,3477,3478,3493,3494,3508,3532,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,5⟩,⟨.covers 75,1,4⟩,⟨.covers 149,1,5⟩,⟨.covers 101,1,4⟩,⟨.covers 197,1,13⟩,⟨.covers 89,1,1⟩,⟨.covers 201,1,5⟩,⟨.covers 777,1,3⟩,⟨.covers 2569,1,14⟩,⟨.covers 2129,1,1⟩,⟨.covers 2145,1,1⟩,⟨.covers 1313,1,3⟩,⟨.covers 142,1,9⟩,⟨.covers 270,1,3⟩,⟨.covers 86,1,2⟩,⟨.covers 2070,1,3⟩,⟨.covers 166,1,5⟩,⟨.covers 154,1,13⟩,⟨.covers 1050,1,2⟩,⟨.covers 106,1,1⟩,⟨.covers 202,1,9⟩,⟨.covers 210,1,18⟩,⟨.covers 2194,1,2⟩,⟨.covers 226,1,8⟩,⟨.covers 1122,1,2⟩,⟨.covers 156,1,9⟩,⟨.covers 108,1,2⟩,⟨.covers 212,1,8⟩,⟨.covers 228,1,16⟩,⟨.covers 3588,1,4⟩,⟨.covers 3336,1,1⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,2⟩,⟨.covers 1424,1,5⟩,⟨.covers 1376,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 928,1,9⟩,⟨.covers 2464,1,5⟩,⟨.covers 1696,1,14⟩,⟨.covers 1824,1,3⟩,⟨.covers 2496,1,12⟩,⟨.covers 1728,1,11⟩,⟨.covers 2752,1,4⟩,⟨.covers 2880,1,2⟩,⟨.covers 1920,1,6⟩,⟨.covers 3456,1,5⟩,⟨.incident 6,8,-4⟩,⟨.incident 7,8,-11⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_043
namespace C13.Global.FastDual40_044
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,11]
def points : Finset C13.Point := {3,6,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,855,871,883,919,935,947,967,979,995,1335,1371,1374,1402,1431,1447,1461,1591,1623,1639,1654,1691,1693,1721,1815,1819,1821,1822,1831,1843,1845,1846,1849,1850,1852,1863,1875,1878,1882,1891,1894,1906,1927,1939,1941,1945,1955,1957,1969,1987,2359,2411,2413,2425,2455,2486,2615,2647,2677,2731,2734,2746,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3277,3278,3292,3308,3351,3379,3405,3433,3478,3532,3607,3635,3669,3726,3754,3788]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 135,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 2224,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 3616,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 1856,1,1⟩,⟨.covers 2880,1,1⟩,⟨.covers 1920,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_044
namespace C13.Global.FastDual40_045
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,8,9]
def points : Finset C13.Point := {3,6,8,9}
def columns : List Code := [254,379,439,506,631,699,701,702,727,743,758,829,830,956,967,979,995,1010,1207,1246,1371,1374,1402,1431,1447,1461,1462,1498,1623,1639,1654,1691,1693,1721,1722,1724,1735,1766,1852,1987,2231,2285,2300,2411,2413,2425,2455,2471,2485,2486,2537,2552,2647,2663,2677,2731,2734,2745,2746,2748,2759,2773,2804,2876,3011,3056,3127,3223,3239,3251,3253,3254,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 263,1,3⟩,⟨.covers 139,1,4⟩,⟨.covers 1059,1,3⟩,⟨.covers 1037,1,10⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,3⟩,⟨.covers 2309,1,5⟩,⟨.covers 89,1,20⟩,⟨.covers 169,1,5⟩,⟨.covers 201,1,3⟩,⟨.covers 777,1,22⟩,⟨.covers 2569,1,6⟩,⟨.covers 593,1,3⟩,⟨.covers 417,1,3⟩,⟨.covers 270,1,12⟩,⟨.covers 1038,1,2⟩,⟨.covers 2062,1,11⟩,⟨.covers 774,1,10⟩,⟨.covers 1286,1,1⟩,⟨.covers 2566,1,3⟩,⟨.covers 154,1,2⟩,⟨.covers 2314,1,20⟩,⟨.covers 1546,1,3⟩,⟨.covers 2098,1,2⟩,⟨.covers 1794,1,13⟩,⟨.covers 2818,1,13⟩,⟨.covers 92,1,5⟩,⟨.covers 2316,1,12⟩,⟨.covers 2196,1,2⟩,⟨.covers 1188,1,1⟩,⟨.covers 1796,1,22⟩,⟨.covers 2820,1,10⟩,⟨.covers 3332,1,2⟩,⟨.covers 216,1,4⟩,⟨.covers 664,1,4⟩,⟨.covers 232,1,2⟩,⟨.covers 3592,1,2⟩,⟨.covers 848,1,7⟩,⟨.covers 1616,1,3⟩,⟨.covers 1424,1,6⟩,⟨.covers 480,1,7⟩,⟨.covers 1376,1,20⟩,⟨.covers 1696,1,6⟩,⟨.covers 3616,1,3⟩,⟨.incident 3,8,-8⟩,⟨.incident 8,8,-7⟩,⟨.incident 9,8,-1⟩]
def bound : Int := 6

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_045
namespace C13.Global.FastDual40_046
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,8,11]
def points : Finset C13.Point := {3,6,8,11}
def columns : List Code := [254,379,439,506,631,695,699,701,702,727,743,758,829,830,919,935,949,950,956,967,979,995,1010,1207,1246,1371,1374,1402,1431,1447,1461,1462,1498,1591,1623,1639,1654,1687,1691,1693,1694,1703,1715,1717,1718,1721,1722,1724,1735,1750,1766,1822,1852,1882,1927,1942,1957,1972,1987,2002,2231,2285,2300,2411,2413,2425,2455,2486,2537,2552,2615,2647,2677,2711,2731,2734,2739,2742,2746,2773,2804,2921,2966,3056,3127,3223,3251,3254,3277,3278,3292,3308,3433,3478,3607,3635,3669,3726,3734,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 263,1,5⟩,⟨.covers 1031,1,3⟩,⟨.covers 2055,1,8⟩,⟨.covers 139,1,10⟩,⟨.covers 1059,1,3⟩,⟨.covers 2563,1,5⟩,⟨.covers 525,1,8⟩,⟨.covers 149,1,3⟩,⟨.covers 197,1,1⟩,⟨.covers 773,1,5⟩,⟨.covers 2309,1,2⟩,⟨.covers 89,1,11⟩,⟨.covers 201,1,14⟩,⟨.covers 2097,1,2⟩,⟨.covers 593,1,2⟩,⟨.covers 417,1,3⟩,⟨.covers 705,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 2062,1,15⟩,⟨.covers 778,1,11⟩,⟨.covers 2314,1,17⟩,⟨.covers 338,1,1⟩,⟨.covers 1122,1,4⟩,⟨.covers 2818,1,17⟩,⟨.covers 3330,1,17⟩,⟨.covers 92,1,10⟩,⟨.covers 2316,1,15⟩,⟨.covers 1124,1,1⟩,⟨.covers 2824,1,17⟩,⟨.covers 3336,1,14⟩,⟨.covers 624,1,5⟩,⟨.covers 2160,1,2⟩,⟨.covers 1328,1,8⟩,⟨.covers 2384,1,1⟩,⟨.covers 3152,1,5⟩,⟨.covers 480,1,1⟩,⟨.covers 736,1,5⟩,⟨.covers 3168,1,4⟩,⟨.covers 3232,1,10⟩,⟨.covers 1824,1,5⟩,⟨.covers 3616,1,5⟩,⟨.covers 1472,1,11⟩,⟨.covers 2752,1,2⟩,⟨.covers 3648,1,8⟩,⟨.incident 8,8,-2⟩,⟨.incident 11,8,-5⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_046
namespace C13.Global.FastDual40_047
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,9,11]
def points : Finset C13.Point := {3,6,9,11}
def columns : List Code := [254,379,439,506,631,699,701,702,727,743,758,829,830,855,871,953,954,956,967,979,995,1010,1207,1246,1335,1371,1374,1402,1431,1447,1459,1461,1462,1498,1623,1639,1654,1691,1693,1721,1722,1724,1735,1766,1821,1852,1863,1894,1945,1976,1987,2018,2231,2285,2300,2359,2411,2413,2425,2455,2483,2486,2537,2552,2647,2677,2731,2734,2746,2773,2804,2901,2986,3056,3127,3223,3251,3254,3277,3278,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 2055,1,2⟩,⟨.covers 1035,1,9⟩,⟨.covers 99,1,6⟩,⟨.covers 2307,1,6⟩,⟨.covers 1539,1,1⟩,⟨.covers 525,1,10⟩,⟨.covers 389,1,1⟩,⟨.covers 89,1,9⟩,⟨.covers 201,1,18⟩,⟨.covers 777,1,8⟩,⟨.covers 2569,1,18⟩,⟨.covers 2097,1,2⟩,⟨.covers 657,1,6⟩,⟨.covers 705,1,3⟩,⟨.covers 897,1,2⟩,⟨.covers 270,1,15⟩,⟨.covers 1038,1,3⟩,⟨.covers 2062,1,9⟩,⟨.covers 774,1,3⟩,⟨.covers 2566,1,6⟩,⟨.covers 202,1,5⟩,⟨.covers 2314,1,5⟩,⟨.covers 2194,1,1⟩,⟨.covers 2818,1,12⟩,⟨.covers 3330,1,2⟩,⟨.covers 3586,1,18⟩,⟨.covers 2316,1,18⟩,⟨.covers 2572,1,2⟩,⟨.covers 420,1,11⟩,⟨.covers 1572,1,2⟩,⟨.covers 2820,1,11⟩,⟨.covers 3588,1,11⟩,⟨.covers 120,1,3⟩,⟨.covers 216,1,9⟩,⟨.covers 664,1,2⟩,⟨.covers 1584,1,9⟩,⟨.covers 3216,1,8⟩,⟨.covers 2656,1,9⟩,⟨.covers 3168,1,18⟩,⟨.covers 1824,1,6⟩,⟨.covers 1728,1,5⟩,⟨.covers 2752,1,2⟩,⟨.incident 3,8,-6⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source40.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source40.rootCodes link40 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual40_047
