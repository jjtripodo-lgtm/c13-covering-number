import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source39
namespace C13.Global.FastDual39_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,9,10]
def points : Finset C13.Point := {1,2,9,10}
def columns : List Code := [247,251,253,254,445,475,499,501,502,505,506,508,637,747,755,757,758,761,762,764,829,885,892,953,956,971,979,985,995,1002,1009,1010,1012,1016,1147,1261,1267,1269,1270,1273,1274,1276,1371,1395,1402,1453,1461,1465,1497,1498,1509,1516,1521,1522,1524,1528,1639,1646,1654,1721,1753,1766,1777,1778,1780,1784,1894,1945,2032,2235,2269,2291,2293,2294,2297,2298,2300,2425,2455,2459,2461,2462,2483,2485,2486,2489,2490,2492,2515,2517,2518,2521,2522,2524,2537,2545,2546,2548,2552,2653,2677,2684,2731,2745,2746,2773,2777,2787,2794,2801,2802,2804,2808,2845,2876,2901,2932,2955,2969,2986,3000,3011,3025,3042,3056,3131,3187,3194,3251,3257,3277,3289,3292,3301,3308,3313,3314,3316,3320,3355,3379,3418,3442,3469,3481,3493,3505,3532,3544,3556,3568,3686,3737,3824]
def rows : List LinearRow := [⟨.covers 263,1,19⟩,⟨.covers 519,1,19⟩,⟨.covers 75,1,8⟩,⟨.covers 523,1,5⟩,⟨.covers 1035,1,4⟩,⟨.covers 83,1,5⟩,⟨.covers 163,1,2⟩,⟨.covers 1283,1,1⟩,⟨.covers 2563,1,7⟩,⟨.covers 77,1,5⟩,⟨.covers 525,1,4⟩,⟨.covers 1037,1,6⟩,⟨.covers 197,1,2⟩,⟨.covers 773,1,11⟩,⟨.covers 1073,1,2⟩,⟨.covers 593,1,2⟩,⟨.covers 2145,1,9⟩,⟨.covers 1185,1,4⟩,⟨.covers 1793,1,19⟩,⟨.covers 3585,1,19⟩,⟨.covers 270,1,19⟩,⟨.covers 526,1,19⟩,⟨.covers 86,1,4⟩,⟨.covers 166,1,6⟩,⟨.covers 774,1,19⟩,⟨.covers 2566,1,19⟩,⟨.covers 2090,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 3082,1,12⟩,⟨.covers 1074,1,1⟩,⟨.covers 338,1,1⟩,⟨.covers 1106,1,1⟩,⟨.covers 674,1,1⟩,⟨.covers 450,1,5⟩,⟨.covers 2818,1,6⟩,⟨.covers 3330,1,3⟩,⟨.covers 92,1,3⟩,⟨.covers 172,1,1⟩,⟨.covers 1292,1,7⟩,⟨.covers 2572,1,3⟩,⟨.covers 564,1,3⟩,⟨.covers 596,1,1⟩,⟨.covers 2132,1,1⟩,⟨.covers 420,1,2⟩,⟨.covers 1220,1,1⟩,⟨.covers 2244,1,3⟩,⟨.covers 2820,1,2⟩,⟨.covers 3332,1,6⟩,⟨.covers 184,1,4⟩,⟨.covers 568,1,1⟩,⟨.covers 360,1,9⟩,⟨.covers 2152,1,2⟩,⟨.covers 680,1,3⟩,⟨.covers 3144,1,2⟩,⟨.covers 1328,1,7⟩,⟨.covers 2608,1,4⟩,⟨.covers 2256,1,4⟩,⟨.covers 848,1,2⟩,⟨.covers 1616,1,10⟩,⟨.covers 3152,1,1⟩,⟨.covers 2848,1,7⟩,⟨.covers 3360,1,7⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source39.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source39.rootCodes link39 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual39_000
namespace C13.Global.FastDual39_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,10,11]
def points : Finset C13.Point := {2,3,10,11}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,823,827,829,830,883,885,886,889,890,892,947,949,950,953,954,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1395,1402,1447,1459,1461,1497,1498,1509,1510,1521,1522,1524,1528,1639,1651,1654,1691,1715,1721,1753,1754,1765,1766,1777,1778,1780,1784,1819,1831,1843,1882,1894,1906,1945,1957,1969,2008,2020,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2419,2425,2455,2483,2486,2517,2518,2537,2538,2545,2546,2548,2552,2647,2675,2677,2731,2739,2746,2773,2774,2793,2794,2801,2802,2804,2808,2839,2859,2867,2901,2921,2929,2966,2986,2994,3028,3048,3056,3187,3251,3277,3278,3292,3308,3313,3314,3316,3320,3379,3532,3568,3635,3788,3824]
def rows : List LinearRow := [⟨.covers 71,1,4⟩,⟨.covers 1031,1,3⟩,⟨.covers 2055,1,4⟩,⟨.covers 139,1,5⟩,⟨.covers 1035,1,5⟩,⟨.covers 2059,1,3⟩,⟨.covers 269,1,22⟩,⟨.covers 1037,1,22⟩,⟨.covers 101,1,4⟩,⟨.covers 389,1,2⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,1⟩,⟨.covers 89,1,2⟩,⟨.covers 169,1,6⟩,⟨.covers 1289,1,7⟩,⟨.covers 2569,1,2⟩,⟨.covers 2129,1,3⟩,⟨.covers 1169,1,3⟩,⟨.covers 2145,1,2⟩,⟨.covers 1185,1,1⟩,⟨.covers 705,1,7⟩,⟨.covers 3329,1,16⟩,⟨.covers 3585,1,16⟩,⟨.covers 270,1,22⟩,⟨.covers 1038,1,22⟩,⟨.covers 166,1,3⟩,⟨.covers 1286,1,4⟩,⟨.covers 2566,1,3⟩,⟨.covers 154,1,1⟩,⟨.covers 106,1,5⟩,⟨.covers 2314,1,6⟩,⟨.covers 1546,1,5⟩,⟨.covers 114,1,2⟩,⟨.covers 178,1,2⟩,⟨.covers 1106,1,2⟩,⟨.covers 2194,1,2⟩,⟨.covers 2210,1,1⟩,⟨.covers 450,1,5⟩,⟨.covers 706,1,4⟩,⟨.covers 172,1,10⟩,⟨.covers 1292,1,22⟩,⟨.covers 1548,1,22⟩,⟨.covers 596,1,1⟩,⟨.covers 404,1,1⟩,⟨.covers 2196,1,2⟩,⟨.covers 612,1,3⟩,⟨.covers 420,1,3⟩,⟨.covers 1796,1,8⟩,⟨.covers 344,1,2⟩,⟨.covers 1112,1,4⟩,⟨.covers 664,1,3⟩,⟨.covers 360,1,6⟩,⟨.covers 680,1,5⟩,⟨.covers 2824,1,9⟩,⟨.covers 688,1,1⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,3⟩,⟨.covers 1424,1,4⟩,⟨.covers 2704,1,3⟩,⟨.covers 1808,1,6⟩,⟨.covers 2832,1,5⟩,⟨.covers 1376,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 3168,1,7⟩,⟨.covers 1696,1,1⟩,⟨.covers 2848,1,2⟩,⟨.incident 3,8,-7⟩]
def bound : Int := 17

theorem column_mask : listMask columns = restrictMask universeMask Source39.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source39.rootCodes link39 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual39_001
