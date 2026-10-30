import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source31
namespace C13.Global.FastDual31_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,11]
def points : Finset C13.Point := {3,7,9,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1367,1371,1373,1374,1383,1395,1397,1398,1401,1402,1404,1431,1447,1461,1479,1493,1509,1623,1639,1653,1654,1691,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2647,2677,2731,2734,2746,2794,2901,2986,3127,3159,3187,3189,3277,3278,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 1038,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 1584,1,1⟩,⟨.covers 2608,1,1⟩,⟨.covers 1248,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 1920,1,1⟩,⟨.covers 3456,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source31.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source31.rootCodes link31 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual31_008
namespace C13.Global.FastDual31_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,10,11]
def points : Finset C13.Point := {3,7,10,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,823,827,829,830,855,871,883,885,886,889,890,892,919,935,947,967,979,995,1143,1245,1335,1371,1374,1383,1395,1398,1402,1447,1461,1509,1591,1639,1651,1654,1691,1693,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2615,2647,2675,2677,2731,2734,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3187,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 135,1,8⟩,⟨.covers 1031,1,3⟩,⟨.covers 2055,1,3⟩,⟨.covers 75,1,10⟩,⟨.covers 1035,1,1⟩,⟨.covers 269,1,9⟩,⟨.covers 525,1,2⟩,⟨.covers 1541,1,4⟩,⟨.covers 169,1,3⟩,⟨.covers 2569,1,8⟩,⟨.covers 3081,1,10⟩,⟨.covers 2625,1,1⟩,⟨.covers 3329,1,10⟩,⟨.covers 3585,1,10⟩,⟨.covers 142,1,5⟩,⟨.covers 270,1,9⟩,⟨.covers 526,1,2⟩,⟨.covers 2566,1,4⟩,⟨.covers 3078,1,5⟩,⟨.covers 154,1,8⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,2⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 156,1,5⟩,⟨.covers 116,1,1⟩,⟨.covers 180,1,3⟩,⟨.covers 596,1,1⟩,⟨.covers 612,1,2⟩,⟨.covers 1796,1,4⟩,⟨.covers 2820,1,4⟩,⟨.covers 3332,1,10⟩,⟨.covers 3588,1,10⟩,⟨.covers 120,1,1⟩,⟨.covers 1800,1,8⟩,⟨.covers 2824,1,2⟩,⟨.covers 1136,1,5⟩,⟨.covers 2160,1,5⟩,⟨.covers 1200,1,8⟩,⟨.covers 720,1,10⟩,⟨.covers 2256,1,5⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,1⟩,⟨.covers 2704,1,3⟩,⟨.covers 736,1,10⟩,⟨.covers 1376,1,4⟩,⟨.covers 2464,1,8⟩,⟨.covers 3232,1,10⟩,⟨.covers 1920,1,3⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source31.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source31.rootCodes link31 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual31_009
