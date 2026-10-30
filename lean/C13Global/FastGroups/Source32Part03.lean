import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source32
namespace C13.Global.FastDual32_024
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,10,11]
def points : Finset C13.Point := {3,7,10,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,823,827,829,830,855,871,883,885,886,889,890,892,919,935,947,967,979,995,1143,1245,1335,1371,1374,1383,1395,1398,1402,1447,1461,1509,1591,1639,1651,1654,1691,1693,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2615,2647,2675,2677,2731,2734,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3187,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 135,1,3⟩,⟨.covers 1031,1,3⟩,⟨.covers 2055,1,2⟩,⟨.covers 75,1,6⟩,⟨.covers 1035,1,5⟩,⟨.covers 269,1,5⟩,⟨.covers 525,1,6⟩,⟨.covers 149,1,1⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,3⟩,⟨.covers 169,1,6⟩,⟨.covers 2569,1,5⟩,⟨.covers 3081,1,10⟩,⟨.covers 3329,1,10⟩,⟨.covers 3585,1,10⟩,⟨.covers 270,1,5⟩,⟨.covers 526,1,5⟩,⟨.covers 1038,1,1⟩,⟨.covers 1286,1,4⟩,⟨.covers 2566,1,5⟩,⟨.covers 3078,1,6⟩,⟨.covers 2314,1,5⟩,⟨.covers 1546,1,6⟩,⟨.covers 3082,1,3⟩,⟨.covers 210,1,4⟩,⟨.covers 226,1,5⟩,⟨.covers 2316,1,1⟩,⟨.covers 180,1,6⟩,⟨.covers 596,1,2⟩,⟨.covers 612,1,2⟩,⟨.covers 120,1,5⟩,⟨.covers 184,1,5⟩,⟨.covers 2824,1,1⟩,⟨.covers 3336,1,2⟩,⟨.covers 3592,1,8⟩,⟨.covers 1136,1,5⟩,⟨.covers 2160,1,6⟩,⟨.covers 720,1,7⟩,⟨.covers 1616,1,1⟩,⟨.covers 1424,1,3⟩,⟨.covers 2704,1,6⟩,⟨.covers 3216,1,10⟩,⟨.covers 736,1,6⟩,⟨.covers 1248,1,9⟩,⟨.covers 1376,1,1⟩,⟨.covers 2464,1,5⟩,⟨.covers 3232,1,1⟩,⟨.covers 2496,1,7⟩,⟨.covers 1728,1,2⟩,⟨.covers 1856,1,3⟩,⟨.covers 2880,1,5⟩,⟨.covers 1920,1,7⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source32.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source32.rootCodes link32 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual32_024
namespace C13.Global.FastDual32_025
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,7,10,11]
def points : Finset C13.Point := {6,7,10,11}
def columns : List Code := [127,191,223,239,319,351,367,379,415,431,439,463,575,607,623,631,671,687,699,719,799,815,823,827,829,830,847,855,859,871,875,883,911,919,923,935,939,947,967,971,979,995,1087,1119,1135,1150,1183,1199,1213,1231,1311,1327,1335,1339,1359,1371,1374,1390,1402,1423,1437,1447,1453,1461,1567,1583,1591,1595,1615,1630,1639,1646,1654,1679,1691,1693,1709,1721,1807,1819,1831,1843,1870,1882,1894,1906,1933,1945,1957,1969,2111,2143,2159,2173,2207,2223,2238,2255,2335,2351,2359,2363,2383,2397,2411,2413,2425,2447,2455,2462,2478,2486,2591,2607,2615,2619,2639,2647,2653,2669,2677,2703,2718,2731,2734,2746,2831,2839,2859,2867,2893,2901,2921,2929,2958,2966,2986,2994,3103,3119,3127,3131,3151,3215,3277,3278,3292,3308,3343,3379,3532,3599,3635,3788]
def rows : List LinearRow := [⟨.covers 197,1,1⟩,⟨.covers 86,1,1⟩,⟨.covers 166,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 284,1,1⟩,⟨.covers 556,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 720,1,2⟩,⟨.covers 1232,1,2⟩,⟨.covers 2384,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 736,1,2⟩,⟨.covers 1248,1,2⟩,⟨.covers 1376,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 3360,1,2⟩,⟨.covers 3616,1,2⟩,⟨.covers 1472,1,2⟩,⟨.covers 1728,1,2⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source32.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source32.rootCodes link32 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual32_025
