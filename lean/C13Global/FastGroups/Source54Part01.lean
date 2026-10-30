import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source54
namespace C13.Global.FastDual54_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,10]
def points : Finset C13.Point := {2,7,9,10}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1639,1646,1654,1691,1721,1753,1894,1945,2171,2270,2363,2395,2411,2419,2425,2426,2455,2462,2486,2518,2647,2653,2677,2678,2684,2715,2731,2746,2763,2794,2845,2876,2901,2932,2955,2986,3011,3042,3131,3163,3187,3194,3277,3278,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 2055,1,3⟩,⟨.covers 1035,1,5⟩,⟨.covers 163,1,2⟩,⟨.covers 1283,1,5⟩,⟨.covers 1539,1,13⟩,⟨.covers 2563,1,3⟩,⟨.covers 525,1,3⟩,⟨.covers 2061,1,2⟩,⟨.covers 53,1,1⟩,⟨.covers 197,1,12⟩,⟨.covers 773,1,1⟩,⟨.covers 1541,1,5⟩,⟨.covers 2097,1,3⟩,⟨.covers 3105,1,2⟩,⟨.covers 2625,1,1⟩,⟨.covers 1793,1,7⟩,⟨.covers 3585,1,18⟩,⟨.covers 46,1,1⟩,⟨.covers 198,1,3⟩,⟨.covers 1286,1,7⟩,⟨.covers 330,1,3⟩,⟨.covers 778,1,3⟩,⟨.covers 3082,1,5⟩,⟨.covers 226,1,3⟩,⟨.covers 300,1,2⟩,⟨.covers 1292,1,12⟩,⟨.covers 1548,1,16⟩,⟨.covers 2572,1,1⟩,⟨.covers 228,1,2⟩,⟨.covers 1796,1,10⟩,⟨.covers 3588,1,18⟩,⟨.covers 2600,1,2⟩,⟨.covers 1352,1,2⟩,⟨.covers 1136,1,5⟩,⟨.covers 2224,1,3⟩,⟨.covers 1328,1,5⟩,⟨.covers 2608,1,2⟩,⟨.covers 1232,1,9⟩,⟨.covers 848,1,4⟩,⟨.covers 1616,1,8⟩,⟨.covers 3152,1,5⟩,⟨.covers 912,1,2⟩,⟨.covers 1424,1,9⟩,⟨.covers 928,1,1⟩,⟨.covers 1696,1,18⟩,⟨.covers 3232,1,12⟩,⟨.covers 2752,1,2⟩,⟨.incident 9,8,-4⟩,⟨.incident 10,8,-11⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source54.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source54.rootCodes link54 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual54_008
namespace C13.Global.FastDual54_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,10,11]
def points : Finset C13.Point := {2,7,10,11}
def columns : List Code := [379,439,631,635,637,638,699,731,747,823,827,829,830,859,875,883,885,886,889,890,892,923,939,947,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1595,1627,1639,1646,1651,1654,1658,1691,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2619,2647,2653,2667,2675,2677,2681,2731,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3187,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 1031,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 300,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3332,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source54.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source54.rootCodes link54 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual54_009
