import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source22
namespace C13.Global.FastDual22_016
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,8]
def points : Finset C13.Point := {3,6,7,8}
def columns : List Code := [379,439,631,699,829,830,919,935,967,979,995,1371,1374,1402,1431,1447,1461,1591,1623,1639,1654,1691,1693,1721,1822,1852,1882,1927,1957,1987,2411,2413,2425,2455,2471,2486,2615,2647,2663,2677,2731,2734,2746,2861,2876,2921,2951,2966,3011,3127,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3607,3623,3635,3637,3638,3655,3669,3670,3685,3686,3700,3723,3725,3726,3737,3738,3740,3753,3754,3756,3768,3788]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 135,1,2⟩,⟨.covers 139,1,1⟩,⟨.covers 1035,1,2⟩,⟨.covers 2059,1,1⟩,⟨.covers 2067,1,1⟩,⟨.covers 77,1,9⟩,⟨.covers 149,1,4⟩,⟨.covers 101,1,4⟩,⟨.covers 197,1,4⟩,⟨.covers 89,1,10⟩,⟨.covers 1049,1,2⟩,⟨.covers 169,1,3⟩,⟨.covers 777,1,7⟩,⟨.covers 2129,1,3⟩,⟨.covers 1313,1,3⟩,⟨.covers 78,1,4⟩,⟨.covers 142,1,1⟩,⟨.covers 270,1,7⟩,⟨.covers 86,1,3⟩,⟨.covers 166,1,3⟩,⟨.covers 1062,1,1⟩,⟨.covers 198,1,8⟩,⟨.covers 154,1,2⟩,⟨.covers 106,1,4⟩,⟨.covers 2090,1,2⟩,⟨.covers 2314,1,7⟩,⟨.covers 210,1,8⟩,⟨.covers 2322,1,2⟩,⟨.covers 226,1,17⟩,⟨.covers 1570,1,1⟩,⟨.covers 3330,1,3⟩,⟨.covers 212,1,13⟩,⟨.covers 228,1,14⟩,⟨.covers 184,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 3592,1,3⟩,⟨.covers 848,1,9⟩,⟨.covers 2384,1,1⟩,⟨.covers 1616,1,4⟩,⟨.covers 1424,1,3⟩,⟨.covers 2704,1,2⟩,⟨.covers 2832,1,7⟩,⟨.covers 1376,1,10⟩,⟨.covers 2656,1,3⟩,⟨.covers 2464,1,4⟩,⟨.covers 1696,1,1⟩,⟨.covers 1824,1,7⟩,⟨.covers 1472,1,17⟩,⟨.covers 2496,1,5⟩,⟨.covers 2752,1,8⟩,⟨.covers 2880,1,4⟩,⟨.covers 3648,1,3⟩,⟨.covers 3456,1,3⟩,⟨.incident 6,8,-7⟩,⟨.incident 7,8,-4⟩,⟨.incident 8,8,-4⟩]
def bound : Int := 3

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_016
namespace C13.Global.FastDual22_017
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,9]
def points : Finset C13.Point := {3,6,7,9}
def columns : List Code := [379,439,631,699,829,830,855,871,967,979,995,1335,1371,1374,1402,1431,1447,1461,1623,1639,1654,1691,1693,1721,1821,1852,1863,1894,1945,1987,2359,2411,2413,2425,2455,2471,2486,2647,2663,2677,2731,2734,2746,2862,2876,2887,2901,2986,3011,3127,3277,3278,3292,3308,3351,3367,3379,3381,3382,3403,3405,3406,3417,3418,3420,3433,3434,3436,3448,3463,3477,3478,3493,3494,3508,3532,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 135,1,3⟩,⟨.covers 75,1,1⟩,⟨.covers 2059,1,2⟩,⟨.covers 141,1,11⟩,⟨.covers 149,1,3⟩,⟨.covers 101,1,4⟩,⟨.covers 1061,1,2⟩,⟨.covers 89,1,3⟩,⟨.covers 169,1,2⟩,⟨.covers 201,1,1⟩,⟨.covers 777,1,8⟩,⟨.covers 2569,1,10⟩,⟨.covers 2577,1,2⟩,⟨.covers 2145,1,2⟩,⟨.covers 1313,1,2⟩,⟨.covers 142,1,1⟩,⟨.covers 526,1,8⟩,⟨.covers 86,1,4⟩,⟨.covers 2070,1,2⟩,⟨.covers 166,1,3⟩,⟨.covers 198,1,11⟩,⟨.covers 154,1,13⟩,⟨.covers 1050,1,2⟩,⟨.covers 106,1,1⟩,⟨.covers 210,1,14⟩,⟨.covers 2322,1,2⟩,⟨.covers 226,1,17⟩,⟨.covers 1122,1,2⟩,⟨.covers 3586,1,2⟩,⟨.covers 212,1,12⟩,⟨.covers 228,1,12⟩,⟨.covers 120,1,1⟩,⟨.covers 3336,1,2⟩,⟨.covers 1616,1,4⟩,⟨.covers 912,1,3⟩,⟨.covers 1424,1,3⟩,⟨.covers 2704,1,2⟩,⟨.covers 2832,1,8⟩,⟨.covers 2656,1,2⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,13⟩,⟨.covers 1824,1,8⟩,⟨.covers 1472,1,6⟩,⟨.covers 1728,1,10⟩,⟨.covers 2752,1,17⟩,⟨.covers 3648,1,4⟩,⟨.covers 3456,1,3⟩,⟨.incident 6,8,-2⟩,⟨.incident 7,8,-6⟩,⟨.incident 9,8,-5⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_017
namespace C13.Global.FastDual22_018
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,11]
def points : Finset C13.Point := {3,6,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,855,871,883,919,935,947,967,979,995,1335,1371,1374,1402,1431,1447,1461,1591,1623,1639,1654,1691,1693,1721,1815,1819,1821,1822,1831,1843,1845,1846,1849,1850,1852,1863,1875,1878,1882,1891,1894,1906,1927,1939,1941,1945,1955,1957,1969,1987,2359,2411,2413,2425,2455,2486,2615,2647,2677,2731,2734,2746,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3277,3278,3292,3308,3351,3379,3405,3433,3478,3532,3607,3635,3669,3726,3754,3788]
def rows : List LinearRow := [⟨.covers 2055,1,11⟩,⟨.covers 1035,1,11⟩,⟨.covers 77,1,3⟩,⟨.covers 525,1,11⟩,⟨.covers 101,1,8⟩,⟨.covers 201,1,8⟩,⟨.covers 2569,1,11⟩,⟨.covers 270,1,11⟩,⟨.covers 166,1,8⟩,⟨.covers 198,1,11⟩,⟨.covers 106,1,11⟩,⟨.covers 210,1,11⟩,⟨.covers 226,1,11⟩,⟨.covers 172,1,3⟩,⟨.covers 116,1,3⟩,⟨.covers 180,1,3⟩,⟨.covers 212,1,5⟩,⟨.covers 228,1,8⟩,⟨.covers 1316,1,3⟩,⟨.covers 1572,1,3⟩,⟨.covers 184,1,11⟩,⟨.covers 2384,1,11⟩,⟨.covers 1616,1,5⟩,⟨.covers 3152,1,5⟩,⟨.covers 1424,1,5⟩,⟨.covers 3360,1,11⟩,⟨.covers 3616,1,11⟩,⟨.covers 2496,1,5⟩,⟨.covers 2752,1,11⟩,⟨.covers 1856,1,5⟩,⟨.covers 1920,1,5⟩,⟨.covers 2944,1,11⟩,⟨.covers 3456,1,5⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_018
namespace C13.Global.FastDual22_019
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,8,9]
def points : Finset C13.Point := {3,6,8,9}
def columns : List Code := [254,379,439,506,631,699,701,702,727,743,758,829,830,956,967,979,995,1010,1207,1246,1371,1374,1402,1431,1447,1461,1462,1498,1623,1639,1654,1691,1693,1721,1722,1724,1735,1766,1852,1987,2231,2285,2300,2411,2413,2425,2455,2471,2485,2486,2537,2552,2647,2663,2677,2731,2734,2745,2746,2748,2759,2773,2804,2876,3011,3056,3127,3223,3239,3251,3253,3254,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 263,1,3⟩,⟨.covers 139,1,8⟩,⟨.covers 1037,1,12⟩,⟨.covers 101,1,3⟩,⟨.covers 89,1,20⟩,⟨.covers 169,1,6⟩,⟨.covers 201,1,8⟩,⟨.covers 777,1,20⟩,⟨.covers 2569,1,5⟩,⟨.covers 593,1,1⟩,⟨.covers 657,1,2⟩,⟨.covers 2577,1,3⟩,⟨.covers 417,1,3⟩,⟨.covers 1038,1,1⟩,⟨.covers 2062,1,19⟩,⟨.covers 774,1,1⟩,⟨.covers 778,1,19⟩,⟨.covers 2314,1,20⟩,⟨.covers 1546,1,4⟩,⟨.covers 2098,1,7⟩,⟨.covers 1570,1,1⟩,⟨.covers 2594,1,1⟩,⟨.covers 1794,1,7⟩,⟨.covers 2818,1,7⟩,⟨.covers 92,1,2⟩,⟨.covers 1292,1,17⟩,⟨.covers 2316,1,16⟩,⟨.covers 212,1,1⟩,⟨.covers 216,1,14⟩,⟨.covers 664,1,4⟩,⟨.covers 1176,1,2⟩,⟨.covers 232,1,3⟩,⟨.covers 1800,1,3⟩,⟨.covers 2824,1,4⟩,⟨.covers 3592,1,4⟩,⟨.covers 1616,1,3⟩,⟨.covers 912,1,3⟩,⟨.covers 1424,1,3⟩,⟨.covers 1376,1,20⟩,⟨.covers 928,1,4⟩,⟨.covers 1696,1,6⟩,⟨.covers 3616,1,4⟩,⟨.covers 3456,1,3⟩,⟨.incident 3,8,-13⟩,⟨.incident 9,8,-1⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_019
namespace C13.Global.FastDual22_020
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,8,11]
def points : Finset C13.Point := {3,6,8,11}
def columns : List Code := [254,379,439,506,631,695,699,701,702,727,743,758,829,830,919,935,949,950,956,967,979,995,1010,1207,1246,1371,1374,1402,1431,1447,1461,1462,1498,1591,1623,1639,1654,1687,1691,1693,1694,1703,1715,1717,1718,1721,1722,1724,1735,1750,1766,1822,1852,1882,1927,1942,1957,1972,1987,2002,2231,2285,2300,2411,2413,2425,2455,2486,2537,2552,2615,2647,2677,2711,2731,2734,2739,2742,2746,2773,2804,2921,2966,3056,3127,3223,3251,3254,3277,3278,3292,3308,3433,3478,3607,3635,3669,3726,3734,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 201,1,2⟩,⟨.covers 2569,1,1⟩,⟨.covers 2062,1,2⟩,⟨.covers 2314,1,2⟩,⟨.covers 2818,1,2⟩,⟨.covers 3330,1,2⟩,⟨.covers 2316,1,2⟩,⟨.covers 2824,1,1⟩,⟨.covers 3336,1,2⟩,⟨.covers 2352,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 3616,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 3648,1,1⟩,⟨.incident 11,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_020
namespace C13.Global.FastDual22_021
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,9,11]
def points : Finset C13.Point := {3,6,9,11}
def columns : List Code := [254,379,439,506,631,699,701,702,727,743,758,829,830,855,871,953,954,956,967,979,995,1010,1207,1246,1335,1371,1374,1402,1431,1447,1459,1461,1462,1498,1623,1639,1654,1691,1693,1721,1722,1724,1735,1766,1821,1852,1863,1894,1945,1976,1987,2018,2231,2285,2300,2359,2411,2413,2425,2455,2483,2486,2537,2552,2647,2677,2731,2734,2746,2773,2804,2901,2986,3056,3127,3223,3251,3254,3277,3278,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 75,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 201,1,3⟩,⟨.covers 777,1,1⟩,⟨.covers 2569,1,3⟩,⟨.covers 270,1,2⟩,⟨.covers 1038,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 3082,1,2⟩,⟨.covers 2818,1,3⟩,⟨.covers 3586,1,1⟩,⟨.covers 2316,1,3⟩,⟨.covers 2572,1,3⟩,⟨.covers 568,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 664,1,1⟩,⟨.covers 3168,1,3⟩,⟨.incident 3,8,-3⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_021
namespace C13.Global.FastDual22_022
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,8,9]
def points : Finset C13.Point := {3,7,8,9}
def columns : List Code := [379,381,382,439,471,487,631,699,829,830,892,967,979,995,1143,1245,1371,1374,1401,1402,1404,1431,1447,1461,1479,1509,1623,1639,1653,1654,1691,1693,1721,1753,1852,1987,2167,2286,2411,2413,2425,2426,2428,2455,2471,2486,2503,2518,2647,2663,2677,2678,2731,2734,2746,2794,2876,3011,3127,3159,3175,3187,3189,3190,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,5⟩,⟨.covers 519,1,2⟩,⟨.covers 75,1,9⟩,⟨.covers 1059,1,2⟩,⟨.covers 2061,1,9⟩,⟨.covers 149,1,3⟩,⟨.covers 2069,1,2⟩,⟨.covers 101,1,2⟩,⟨.covers 1061,1,1⟩,⟨.covers 89,1,3⟩,⟨.covers 777,1,13⟩,⟨.covers 2569,1,9⟩,⟨.covers 2097,1,3⟩,⟨.covers 1313,1,2⟩,⟨.covers 2337,1,3⟩,⟨.covers 1038,1,9⟩,⟨.covers 1286,1,3⟩,⟨.covers 2566,1,4⟩,⟨.covers 154,1,9⟩,⟨.covers 778,1,13⟩,⟨.covers 2314,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 1298,1,2⟩,⟨.covers 2322,1,3⟩,⟨.covers 1122,1,1⟩,⟨.covers 1794,1,13⟩,⟨.covers 2818,1,10⟩,⟨.covers 3330,1,3⟩,⟨.covers 156,1,1⟩,⟨.covers 172,1,4⟩,⟨.covers 1548,1,4⟩,⟨.covers 180,1,5⟩,⟨.covers 216,1,2⟩,⟨.covers 232,1,4⟩,⟨.covers 1800,1,9⟩,⟨.covers 2824,1,13⟩,⟨.covers 624,1,1⟩,⟨.covers 2256,1,6⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,4⟩,⟨.covers 912,1,13⟩,⟨.covers 1424,1,1⟩,⟨.covers 864,1,12⟩,⟨.covers 1376,1,9⟩,⟨.covers 2656,1,1⟩,⟨.covers 928,1,2⟩,⟨.covers 2464,1,5⟩,⟨.covers 1696,1,9⟩,⟨.covers 2752,1,4⟩,⟨.covers 3648,1,2⟩,⟨.covers 3456,1,2⟩,⟨.incident 8,8,-5⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_022
namespace C13.Global.FastDual22_023
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,8,11]
def points : Finset C13.Point := {3,7,8,11}
def columns : List Code := [379,381,382,439,471,487,631,699,829,830,889,890,892,919,935,967,979,995,1143,1245,1371,1374,1401,1402,1404,1431,1447,1461,1479,1509,1591,1623,1639,1651,1653,1654,1691,1693,1721,1753,1822,1852,1882,1912,1927,1957,1987,2017,2167,2286,2411,2413,2425,2455,2486,2518,2615,2647,2675,2677,2731,2734,2746,2794,2921,2966,3127,3159,3187,3189,3277,3278,3292,3308,3433,3478,3607,3635,3669,3697,3726,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 1035,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 1328,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 2384,1,1⟩,⟨.covers 928,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 2752,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_023
