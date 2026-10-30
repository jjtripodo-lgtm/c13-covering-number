import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source66
namespace C13.Global.FastDual66_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,6,9]
def points : Finset C13.Point := {0,3,6,9}
def columns : List Code := [702,727,830,954,956,967,979,995,1207,1246,1374,1402,1447,1459,1461,1462,1498,1654,1691,1693,1721,1722,1724,1766,1852,1894,1945,1976,1987,2018,2411,2413,2425,2486,2537,2647,2677,2734,2746,2748,2773,2862,2876,2887,2901,2986,3000,3011,3025,3127,3251,3253,3254,3278,3292,3308,3367,3379,3381,3382,3406,3418,3420,3433,3434,3436,3448,3478,3491,3493,3494,3505,3506,3508,3530,3532,3544,3560,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 43,1,14⟩,⟨.covers 139,1,7⟩,⟨.covers 83,1,3⟩,⟨.covers 163,1,3⟩,⟨.covers 1283,1,3⟩,⟨.covers 1539,1,8⟩,⟨.covers 2563,1,8⟩,⟨.covers 45,1,12⟩,⟨.covers 141,1,12⟩,⟨.covers 53,1,3⟩,⟨.covers 101,1,2⟩,⟨.covers 197,1,8⟩,⟨.covers 773,1,3⟩,⟨.covers 1541,1,1⟩,⟨.covers 3077,1,3⟩,⟨.covers 57,1,9⟩,⟨.covers 201,1,12⟩,⟨.covers 777,1,14⟩,⟨.covers 2569,1,14⟩,⟨.covers 113,1,6⟩,⟨.covers 177,1,3⟩,⟨.covers 225,1,2⟩,⟨.covers 3329,1,3⟩,⟨.covers 2182,1,2⟩,⟨.covers 58,1,6⟩,⟨.covers 202,1,3⟩,⟨.covers 2186,1,1⟩,⟨.covers 778,1,2⟩,⟨.covers 3082,1,2⟩,⟨.covers 338,1,2⟩,⟨.covers 3090,1,3⟩,⟨.covers 3586,1,7⟩,⟨.covers 92,1,2⟩,⟨.covers 172,1,2⟩,⟨.covers 1292,1,6⟩,⟨.covers 1548,1,1⟩,⟨.covers 2572,1,4⟩,⟨.covers 788,1,2⟩,⟨.covers 228,1,7⟩,⟨.covers 420,1,3⟩,⟨.covers 2244,1,1⟩,⟨.covers 184,1,2⟩,⟨.covers 216,1,4⟩,⟨.covers 2824,1,3⟩,⟨.covers 3336,1,2⟩,⟨.covers 2224,1,1⟩,⟨.covers 1328,1,1⟩,⟨.covers 2256,1,2⟩,⟨.covers 848,1,6⟩,⟨.covers 1616,1,7⟩,⟨.covers 864,1,6⟩,⟨.covers 1376,1,1⟩,⟨.covers 2944,1,3⟩,⟨.covers 3456,1,1⟩,⟨.incident 0,8,-4⟩,⟨.incident 3,8,-3⟩]
def bound : Int := 8

theorem column_mask : listMask columns = restrictMask universeMask Source66.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source66.rootCodes link66 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual66_000
namespace C13.Global.FastDual66_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,6,11]
def points : Finset C13.Point := {0,3,6,11}
def columns : List Code := [702,727,830,950,954,956,967,979,995,1207,1246,1374,1402,1447,1459,1461,1462,1498,1654,1687,1691,1693,1694,1715,1717,1718,1721,1722,1724,1750,1766,1822,1846,1850,1852,1878,1882,1894,1906,1927,1939,1941,1942,1945,1946,1948,1955,1957,1958,1969,1970,1972,1976,1987,1990,2002,2018,2411,2413,2425,2486,2537,2647,2677,2734,2742,2746,2773,2901,2921,2929,2966,2986,2994,3127,3251,3254,3278,3292,3308,3379,3433,3478,3506,3532,3560,3607,3635,3669,3726,3734,3754,3762,3788,3796,3851,3859,3913,3921,3978,3986,4040,4048]
def rows : List LinearRow := [⟨.covers 43,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 83,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 773,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 57,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 1289,1,1⟩,⟨.covers 2656,1,1⟩,⟨.incident 0,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source66.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source66.rootCodes link66 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual66_001
namespace C13.Global.FastDual66_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,7,11]
def points : Finset C13.Point := {0,3,7,11}
def columns : List Code := [253,382,487,501,761,830,886,890,892,967,979,995,1009,1374,1398,1402,1404,1447,1461,1509,1654,1691,1693,1721,1753,1822,1846,1850,1852,1878,1882,1884,1894,1906,1908,1912,1927,1939,1941,1945,1955,1957,1969,1987,1989,2001,2017,2167,2286,2300,2411,2413,2419,2421,2425,2486,2518,2548,2647,2675,2677,2734,2746,2794,2808,2901,2921,2929,2966,2986,2994,3056,3127,3187,3189,3278,3292,3308,3379,3433,3441,3478,3532,3540,3607,3635,3669,3697,3726,3754,3788,3816,3851,3859,3913,3921,3978,3986,4040,4048]
def rows : List LinearRow := [⟨.covers 43,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 58,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 3232,1,1⟩,⟨.incident 3,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source66.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source66.rootCodes link66 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual66_002
