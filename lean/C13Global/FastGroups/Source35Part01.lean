import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source35
namespace C13.Global.FastDual35_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,9,11]
def points : Finset C13.Point := {3,6,9,11}
def columns : List Code := [379,439,631,699,701,702,727,743,829,830,855,871,953,954,956,967,979,995,1207,1246,1335,1371,1374,1402,1431,1447,1459,1461,1462,1498,1623,1639,1654,1691,1693,1721,1722,1724,1735,1766,1821,1852,1863,1894,1945,1976,1987,2018,2231,2285,2359,2411,2413,2425,2455,2483,2486,2537,2647,2677,2731,2734,2746,2773,2901,2986,3127,3223,3251,3254,3277,3278,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 2055,1,4⟩,⟨.covers 1035,1,6⟩,⟨.covers 99,1,1⟩,⟨.covers 2307,1,4⟩,⟨.covers 1539,1,2⟩,⟨.covers 2563,1,8⟩,⟨.covers 525,1,5⟩,⟨.covers 89,1,1⟩,⟨.covers 777,1,2⟩,⟨.covers 2569,1,9⟩,⟨.covers 3081,1,14⟩,⟨.covers 1073,1,4⟩,⟨.covers 897,1,1⟩,⟨.covers 1665,1,2⟩,⟨.covers 2817,1,13⟩,⟨.covers 3585,1,13⟩,⟨.covers 270,1,7⟩,⟨.covers 390,1,4⟩,⟨.covers 3078,1,4⟩,⟨.covers 2314,1,10⟩,⟨.covers 3082,1,11⟩,⟨.covers 226,1,4⟩,⟨.covers 1794,1,1⟩,⟨.covers 2818,1,7⟩,⟨.covers 3586,1,6⟩,⟨.covers 108,1,14⟩,⟨.covers 1548,1,3⟩,⟨.covers 2572,1,17⟩,⟨.covers 804,1,3⟩,⟨.covers 1572,1,2⟩,⟨.covers 120,1,5⟩,⟨.covers 184,1,2⟩,⟨.covers 216,1,7⟩,⟨.covers 1136,1,2⟩,⟨.covers 2160,1,2⟩,⟨.covers 2224,1,4⟩,⟨.covers 2352,1,4⟩,⟨.covers 1584,1,3⟩,⟨.covers 2608,1,11⟩,⟨.covers 912,1,5⟩,⟨.covers 3216,1,4⟩,⟨.covers 864,1,1⟩,⟨.covers 2496,1,14⟩,⟨.covers 1728,1,1⟩,⟨.covers 2752,1,13⟩,⟨.incident 3,8,-4⟩,⟨.incident 9,8,-3⟩,⟨.incident 11,8,-7⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source35.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source35.rootCodes link35 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual35_008
namespace C13.Global.FastDual35_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,10,11]
def points : Finset C13.Point := {3,6,10,11}
def columns : List Code := [379,439,631,695,699,701,702,727,743,823,827,829,830,855,871,883,919,935,947,949,950,953,954,956,967,979,995,1207,1246,1335,1371,1374,1402,1447,1459,1461,1498,1591,1639,1654,1691,1693,1703,1715,1717,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2231,2285,2359,2411,2413,2425,2455,2483,2486,2537,2615,2647,2677,2711,2731,2734,2739,2742,2746,2773,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3251,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 1031,1,3⟩,⟨.covers 2055,1,3⟩,⟨.covers 139,1,3⟩,⟨.covers 1035,1,8⟩,⟨.covers 269,1,8⟩,⟨.covers 525,1,3⟩,⟨.covers 389,1,3⟩,⟨.covers 2309,1,3⟩,⟨.covers 1541,1,5⟩,⟨.covers 169,1,3⟩,⟨.covers 1289,1,3⟩,⟨.covers 2569,1,5⟩,⟨.covers 3081,1,11⟩,⟨.covers 3329,1,11⟩,⟨.covers 3585,1,11⟩,⟨.covers 142,1,3⟩,⟨.covers 270,1,8⟩,⟨.covers 526,1,3⟩,⟨.covers 390,1,3⟩,⟨.covers 1286,1,3⟩,⟨.covers 2566,1,5⟩,⟨.covers 3078,1,5⟩,⟨.covers 106,1,11⟩,⟨.covers 3082,1,3⟩,⟨.covers 226,1,8⟩,⟨.covers 450,1,3⟩,⟨.covers 1548,1,3⟩,⟨.covers 116,1,8⟩,⟨.covers 184,1,5⟩,⟨.covers 2824,1,5⟩,⟨.covers 3336,1,8⟩,⟨.covers 3592,1,8⟩,⟨.covers 2160,1,3⟩,⟨.covers 2224,1,3⟩,⟨.covers 720,1,8⟩,⟨.covers 2384,1,8⟩,⟨.covers 1616,1,3⟩,⟨.covers 3152,1,11⟩,⟨.covers 1424,1,8⟩,⟨.covers 2704,1,3⟩,⟨.covers 3168,1,11⟩,⟨.covers 2464,1,5⟩,⟨.covers 1696,1,3⟩,⟨.covers 2496,1,3⟩,⟨.covers 1856,1,8⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source35.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source35.rootCodes link35 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual35_009
