import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source37
namespace C13.Global.FastDual37_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,9,11]
def points : Finset C13.Point := {1,7,9,11}
def columns : List Code := [381,471,637,747,829,861,885,892,967,971,979,995,1143,1147,1149,1150,1213,1245,1261,1341,1367,1371,1373,1374,1389,1395,1397,1398,1401,1402,1404,1437,1453,1461,1485,1493,1509,1597,1629,1639,1646,1653,1654,1660,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2173,2238,2397,2413,2421,2425,2455,2462,2486,2518,2653,2677,2731,2734,2746,2794,2901,2986,3127,3131,3165,3181,3187,3189,3193,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 2055,1,11⟩,⟨.covers 267,1,11⟩,⟨.covers 1539,1,11⟩,⟨.covers 2563,1,11⟩,⟨.covers 525,1,5⟩,⟨.covers 2061,1,5⟩,⟨.covers 297,1,3⟩,⟨.covers 3081,1,5⟩,⟨.covers 2817,1,11⟩,⟨.covers 3585,1,11⟩,⟨.covers 270,1,11⟩,⟨.covers 526,1,5⟩,⟨.covers 198,1,11⟩,⟨.covers 2566,1,5⟩,⟨.covers 3082,1,5⟩,⟨.covers 114,1,11⟩,⟨.covers 2818,1,5⟩,⟨.covers 3586,1,5⟩,⟨.covers 300,1,3⟩,⟨.covers 1548,1,5⟩,⟨.covers 228,1,11⟩,⟨.covers 216,1,11⟩,⟨.covers 1200,1,11⟩,⟨.covers 2352,1,8⟩,⟨.covers 912,1,11⟩,⟨.covers 2704,1,11⟩,⟨.covers 864,1,8⟩,⟨.covers 928,1,3⟩,⟨.covers 2464,1,3⟩,⟨.covers 1824,1,3⟩,⟨.covers 3360,1,3⟩,⟨.covers 2752,1,11⟩,⟨.covers 3456,1,11⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source37.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source37.rootCodes link37 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual37_008
namespace C13.Global.FastDual37_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,9]
def points : Finset C13.Point := {2,3,7,9}
def columns : List Code := [379,439,631,699,829,830,885,886,892,979,995,1371,1395,1401,1402,1447,1461,1509,1639,1653,1654,1691,1721,1753,1852,1894,1908,1945,1987,2001,2411,2419,2425,2426,2455,2486,2518,2647,2677,2678,2731,2746,2794,2876,2901,2932,2986,3011,3042,3187,3277,3278,3292,3308,3379,3403,3411,3417,3418,3427,3433,3434,3441,3442,3448,3463,3477,3478,3493,3494,3508,3525,3526,3532,3540,3556,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 77,1,13⟩,⟨.covers 269,1,17⟩,⟨.covers 149,1,1⟩,⟨.covers 2069,1,3⟩,⟨.covers 101,1,5⟩,⟨.covers 1061,1,1⟩,⟨.covers 1541,1,2⟩,⟨.covers 89,1,4⟩,⟨.covers 1289,1,4⟩,⟨.covers 2569,1,14⟩,⟨.covers 2337,1,4⟩,⟨.covers 1793,1,2⟩,⟨.covers 2817,1,7⟩,⟨.covers 78,1,10⟩,⟨.covers 270,1,6⟩,⟨.covers 86,1,3⟩,⟨.covers 2070,1,2⟩,⟨.covers 1062,1,2⟩,⟨.covers 1286,1,3⟩,⟨.covers 2566,1,3⟩,⟨.covers 154,1,14⟩,⟨.covers 106,1,4⟩,⟨.covers 202,1,4⟩,⟨.covers 778,1,11⟩,⟨.covers 2314,1,4⟩,⟨.covers 210,1,2⟩,⟨.covers 1106,1,4⟩,⟨.covers 226,1,7⟩,⟨.covers 1794,1,5⟩,⟨.covers 156,1,3⟩,⟨.covers 108,1,11⟩,⟨.covers 172,1,2⟩,⟨.covers 2316,1,8⟩,⟨.covers 1548,1,13⟩,⟨.covers 2572,1,9⟩,⟨.covers 116,1,2⟩,⟨.covers 180,1,4⟩,⟨.covers 3332,1,2⟩,⟨.covers 3588,1,5⟩,⟨.covers 120,1,4⟩,⟨.covers 216,1,11⟩,⟨.covers 1800,1,4⟩,⟨.covers 3336,1,4⟩,⟨.covers 912,1,5⟩,⟨.covers 1696,1,14⟩,⟨.incident 2,8,-3⟩,⟨.incident 3,8,-7⟩,⟨.incident 9,8,-4⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source37.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source37.rootCodes link37 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual37_009
namespace C13.Global.FastDual37_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,11]
def points : Finset C13.Point := {2,3,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,883,885,886,889,890,892,947,979,995,1371,1395,1401,1402,1447,1461,1509,1639,1651,1653,1654,1691,1721,1753,1819,1831,1843,1845,1846,1849,1850,1852,1875,1881,1882,1891,1893,1894,1905,1906,1908,1912,1939,1945,1955,1957,1969,1987,2001,2017,2411,2419,2425,2455,2486,2518,2647,2675,2677,2731,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3187,3277,3278,3292,3308,3379,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 75,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 86,1,1⟩,⟨.covers 166,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source37.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source37.rootCodes link37 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual37_010
