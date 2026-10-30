import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source48
namespace C13.Global.FastDual48_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,8,11]
def points : Finset C13.Point := {3,7,8,11}
def columns : List Code := [379,381,382,439,471,487,631,699,829,830,889,890,892,919,935,967,979,995,1143,1245,1371,1374,1401,1402,1404,1431,1447,1461,1479,1509,1591,1623,1639,1651,1653,1654,1691,1693,1721,1753,1822,1852,1882,1912,1927,1957,1987,2017,2167,2286,2411,2413,2425,2455,2486,2518,2615,2647,2675,2677,2731,2734,2746,2794,2921,2966,3127,3159,3187,3189,3277,3278,3292,3308,3433,3478,3607,3635,3669,3697,3726,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 135,1,2⟩,⟨.covers 2055,1,4⟩,⟨.covers 1035,1,6⟩,⟨.covers 1059,1,2⟩,⟨.covers 1283,1,2⟩,⟨.covers 2563,1,4⟩,⟨.covers 525,1,4⟩,⟨.covers 197,1,2⟩,⟨.covers 581,1,2⟩,⟨.covers 773,1,2⟩,⟨.covers 3077,1,4⟩,⟨.covers 169,1,6⟩,⟨.covers 2569,1,2⟩,⟨.covers 3081,1,6⟩,⟨.covers 2817,1,13⟩,⟨.covers 3329,1,8⟩,⟨.covers 78,1,2⟩,⟨.covers 270,1,4⟩,⟨.covers 778,1,2⟩,⟨.covers 2314,1,15⟩,⟨.covers 3082,1,10⟩,⟨.covers 1074,1,2⟩,⟨.covers 226,1,2⟩,⟨.covers 1602,1,2⟩,⟨.covers 1794,1,2⟩,⟨.covers 2818,1,6⟩,⟨.covers 3330,1,15⟩,⟨.covers 92,1,2⟩,⟨.covers 156,1,2⟩,⟨.covers 172,1,8⟩,⟨.covers 556,1,2⟩,⟨.covers 2316,1,15⟩,⟨.covers 2572,1,2⟩,⟨.covers 596,1,2⟩,⟨.covers 1188,1,2⟩,⟨.covers 2160,1,4⟩,⟨.covers 1328,1,6⟩,⟨.covers 2352,1,10⟩,⟨.covers 2608,1,4⟩,⟨.covers 720,1,6⟩,⟨.covers 848,1,2⟩,⟨.covers 3152,1,4⟩,⟨.covers 2704,1,8⟩,⟨.covers 480,1,2⟩,⟨.covers 928,1,4⟩,⟨.covers 2464,1,4⟩,⟨.covers 3232,1,2⟩,⟨.covers 1472,1,2⟩,⟨.covers 2496,1,15⟩,⟨.covers 2752,1,10⟩,⟨.incident 8,8,-2⟩,⟨.incident 11,8,-6⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source48.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source48.rootCodes link48 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual48_008
namespace C13.Global.FastDual48_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,11]
def points : Finset C13.Point := {3,7,9,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1367,1371,1373,1374,1383,1395,1397,1398,1401,1402,1404,1431,1447,1461,1479,1493,1509,1623,1639,1653,1654,1691,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2647,2677,2731,2734,2746,2794,2901,2986,3127,3159,3187,3189,3277,3278,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 519,1,5⟩,⟨.covers 2055,1,5⟩,⟨.covers 1035,1,11⟩,⟨.covers 1059,1,3⟩,⟨.covers 2307,1,5⟩,⟨.covers 525,1,11⟩,⟨.covers 2061,1,11⟩,⟨.covers 2569,1,11⟩,⟨.covers 2817,1,11⟩,⟨.covers 3585,1,11⟩,⟨.covers 1038,1,11⟩,⟨.covers 1062,1,3⟩,⟨.covers 774,1,5⟩,⟨.covers 778,1,5⟩,⟨.covers 210,1,11⟩,⟨.covers 2818,1,5⟩,⟨.covers 3586,1,11⟩,⟨.covers 172,1,3⟩,⟨.covers 2572,1,8⟩,⟨.covers 180,1,11⟩,⟨.covers 120,1,11⟩,⟨.covers 184,1,3⟩,⟨.covers 216,1,11⟩,⟨.covers 1584,1,8⟩,⟨.covers 2608,1,8⟩,⟨.covers 480,1,11⟩,⟨.covers 3168,1,8⟩,⟨.covers 1824,1,3⟩,⟨.covers 3360,1,3⟩,⟨.covers 2752,1,11⟩,⟨.covers 1920,1,11⟩,⟨.covers 3456,1,11⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source48.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source48.rootCodes link48 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual48_009
