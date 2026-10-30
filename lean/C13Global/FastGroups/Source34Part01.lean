import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source34
namespace C13.Global.FastDual34_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,11]
def points : Finset C13.Point := {3,7,9,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1367,1371,1373,1374,1383,1395,1397,1398,1401,1402,1404,1431,1447,1461,1479,1493,1509,1623,1639,1653,1654,1691,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2647,2677,2731,2734,2746,2794,2901,2986,3127,3159,3187,3189,3277,3278,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 1035,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 1038,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 1248,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source34.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source34.rootCodes link34 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual34_008
namespace C13.Global.FastDual34_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,10,11]
def points : Finset C13.Point := {3,7,10,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,823,827,829,830,855,871,883,885,886,889,890,892,919,935,947,967,979,995,1143,1245,1335,1371,1374,1383,1395,1398,1402,1447,1461,1509,1591,1639,1651,1654,1691,1693,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2615,2647,2675,2677,2731,2734,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3187,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 75,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 1248,1,1⟩,⟨.covers 1920,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source34.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source34.rootCodes link34 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual34_009
