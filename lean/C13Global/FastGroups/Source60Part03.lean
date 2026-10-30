import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source60
namespace C13.Global.FastDual60_024
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,10,11]
def points : Finset C13.Point := {3,7,10,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,823,827,829,830,855,871,883,885,886,889,890,892,919,935,947,967,979,995,1143,1245,1335,1371,1374,1383,1395,1398,1402,1447,1461,1509,1591,1639,1651,1654,1691,1693,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2615,2647,2675,2677,2731,2734,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3187,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 2055,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 1248,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_024
namespace C13.Global.FastDual60_025
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [5,6,7,10]
def points : Finset C13.Point := {5,6,7,10}
def columns : List Code := [127,191,223,239,319,351,367,415,431,463,575,607,623,671,687,719,799,815,829,830,847,855,859,911,919,923,967,971,979,1087,1119,1135,1183,1199,1231,1311,1327,1335,1359,1371,1374,1423,1437,1447,1453,1461,1567,1583,1591,1615,1630,1639,1646,1654,1679,1691,1693,1807,1819,1831,1870,1882,1894,1933,1945,1957,2111,2143,2159,2207,2223,2255,2335,2351,2363,2365,2383,2395,2397,2411,2413,2425,2447,2455,2462,2591,2607,2619,2622,2639,2647,2653,2703,2715,2718,2731,2734,2746,2831,2839,2843,2845,2846,2859,2861,2862,2873,2874,2876,2887,2891,2893,2899,2901,2905,2921,2951,2955,2958,2963,2966,2970,2986,3011,3103,3119,3127,3131,3151,3166,3215,3229,3277,3278,3292,3343,3355,3367,3379,3406,3418,3469,3493,3532,3599,3611,3623,3635,3662,3686,3725,3737,3788,3851,3875,3914,3938,3977,4001,4040,4064]
def rows : List LinearRow := [⟨.covers 1035,1,2⟩,⟨.covers 2083,1,1⟩,⟨.covers 581,1,2⟩,⟨.covers 2117,1,2⟩,⟨.covers 1541,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 649,1,1⟩,⟨.covers 1553,1,1⟩,⟨.covers 3089,1,1⟩,⟨.covers 2625,1,2⟩,⟨.covers 1793,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 390,1,2⟩,⟨.covers 2182,1,2⟩,⟨.covers 1286,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 330,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 1298,1,1⟩,⟨.covers 3090,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 2434,1,2⟩,⟨.covers 1794,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 300,1,2⟩,⟨.covers 556,1,2⟩,⟨.covers 1292,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 180,1,3⟩,⟨.covers 212,1,3⟩,⟨.covers 804,1,1⟩,⟨.covers 2628,1,1⟩,⟨.covers 2436,1,1⟩,⟨.covers 120,1,4⟩,⟨.covers 1304,1,1⟩,⟨.covers 1560,1,1⟩,⟨.covers 808,1,2⟩,⟨.covers 3336,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 1136,1,3⟩,⟨.covers 2224,1,3⟩,⟨.covers 464,1,4⟩,⟨.incident 5,8,3⟩,⟨.incident 6,8,3⟩,⟨.incident 7,8,3⟩,⟨.incident 10,8,1⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_025
namespace C13.Global.FastDual60_026
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,7,10,11]
def points : Finset C13.Point := {6,7,10,11}
def columns : List Code := [127,191,223,239,319,351,367,379,415,431,439,463,575,607,623,631,671,687,699,719,799,815,823,827,829,830,847,855,859,871,875,883,911,919,923,935,939,947,967,971,979,995,1087,1119,1135,1150,1183,1199,1213,1231,1311,1327,1335,1339,1359,1371,1374,1390,1402,1423,1437,1447,1453,1461,1567,1583,1591,1595,1615,1630,1639,1646,1654,1679,1691,1693,1709,1721,1807,1819,1831,1843,1870,1882,1894,1906,1933,1945,1957,1969,2111,2143,2159,2173,2207,2223,2238,2255,2335,2351,2359,2363,2383,2397,2411,2413,2425,2447,2455,2462,2478,2486,2591,2607,2615,2619,2639,2647,2653,2669,2677,2703,2718,2731,2734,2746,2831,2839,2859,2867,2893,2901,2921,2929,2958,2966,2986,2994,3103,3119,3127,3131,3151,3215,3277,3278,3292,3308,3343,3379,3532,3599,3635,3788]
def rows : List LinearRow := [⟨.covers 519,1,4⟩,⟨.covers 43,1,4⟩,⟨.covers 149,1,5⟩,⟨.covers 2069,1,1⟩,⟨.covers 101,1,4⟩,⟨.covers 2117,1,2⟩,⟨.covers 389,1,2⟩,⟨.covers 1157,1,3⟩,⟨.covers 2309,1,3⟩,⟨.covers 1541,1,2⟩,⟨.covers 3077,1,3⟩,⟨.covers 1049,1,1⟩,⟨.covers 2089,1,1⟩,⟨.covers 329,1,1⟩,⟨.covers 1289,1,4⟩,⟨.covers 2569,1,3⟩,⟨.covers 86,1,1⟩,⟨.covers 2070,1,3⟩,⟨.covers 1062,1,1⟩,⟨.covers 582,1,4⟩,⟨.covers 390,1,5⟩,⟨.covers 1286,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 1050,1,3⟩,⟨.covers 2090,1,2⟩,⟨.covers 202,1,11⟩,⟨.covers 330,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 3082,1,8⟩,⟨.covers 540,1,8⟩,⟨.covers 300,1,8⟩,⟨.covers 556,1,2⟩,⟨.covers 116,1,5⟩,⟨.covers 180,1,4⟩,⟨.covers 120,1,4⟩,⟨.covers 184,1,4⟩,⟨.covers 1800,1,9⟩,⟨.covers 2824,1,8⟩,⟨.covers 1136,1,4⟩,⟨.covers 2160,1,2⟩,⟨.covers 1200,1,1⟩,⟨.covers 2224,1,5⟩,⟨.covers 464,1,19⟩,⟨.covers 1232,1,19⟩,⟨.covers 2384,1,11⟩,⟨.covers 1616,1,2⟩,⟨.covers 1424,1,5⟩,⟨.covers 2704,1,7⟩,⟨.covers 480,1,19⟩,⟨.covers 1248,1,19⟩,⟨.covers 1376,1,8⟩,⟨.covers 2656,1,4⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,12⟩,⟨.covers 3360,1,19⟩,⟨.covers 3616,1,19⟩,⟨.covers 1472,1,19⟩,⟨.covers 1728,1,19⟩,⟨.covers 1856,1,5⟩,⟨.covers 2880,1,2⟩,⟨.covers 1920,1,1⟩,⟨.covers 2944,1,5⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_026
