import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source27
namespace C13.Global.FastDual27_024
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,10]
def points : Finset C13.Point := {2,7,9,10}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1639,1646,1654,1691,1721,1753,1894,1945,2171,2270,2363,2395,2411,2419,2425,2426,2455,2462,2486,2518,2647,2653,2677,2678,2684,2715,2731,2746,2763,2794,2845,2876,2901,2932,2955,2986,3011,3042,3131,3163,3187,3194,3277,3278,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 135,1,2⟩,⟨.covers 2055,1,5⟩,⟨.covers 139,1,2⟩,⟨.covers 1035,1,4⟩,⟨.covers 1283,1,4⟩,⟨.covers 2563,1,3⟩,⟨.covers 525,1,5⟩,⟨.covers 197,1,14⟩,⟨.covers 773,1,2⟩,⟨.covers 1541,1,17⟩,⟨.covers 2097,1,4⟩,⟨.covers 833,1,1⟩,⟨.covers 2625,1,2⟩,⟨.covers 270,1,7⟩,⟨.covers 1038,1,11⟩,⟨.covers 166,1,5⟩,⟨.covers 1286,1,4⟩,⟨.covers 330,1,4⟩,⟨.covers 3082,1,4⟩,⟨.covers 226,1,4⟩,⟨.covers 1794,1,13⟩,⟨.covers 2818,1,1⟩,⟨.covers 3586,1,17⟩,⟨.covers 1292,1,14⟩,⟨.covers 1548,1,6⟩,⟨.covers 2572,1,3⟩,⟨.covers 116,1,2⟩,⟨.covers 212,1,7⟩,⟨.covers 808,1,3⟩,⟨.covers 2600,1,2⟩,⟨.covers 1800,1,3⟩,⟨.covers 3592,1,13⟩,⟨.covers 1136,1,4⟩,⟨.covers 2224,1,2⟩,⟨.covers 1328,1,4⟩,⟨.covers 1584,1,11⟩,⟨.covers 2608,1,3⟩,⟨.covers 848,1,5⟩,⟨.covers 3152,1,4⟩,⟨.covers 1424,1,11⟩,⟨.covers 928,1,1⟩,⟨.covers 1696,1,2⟩,⟨.covers 3232,1,14⟩,⟨.covers 1728,1,13⟩,⟨.incident 2,8,-4⟩,⟨.incident 9,8,-3⟩,⟨.incident 10,8,-7⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source27.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source27.rootCodes link27 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual27_024
namespace C13.Global.FastDual27_025
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,11]
def points : Finset C13.Point := {2,7,9,11}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1387,1395,1401,1402,1447,1453,1461,1509,1639,1646,1653,1654,1660,1691,1707,1721,1739,1753,1838,1852,1894,1908,1931,1945,1987,2001,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2647,2653,2677,2731,2746,2794,2901,2986,3131,3179,3187,3193,3277,3278,3292,3308,3371,3379,3433,3441,3470,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 1031,1,4⟩,⟨.covers 2055,1,9⟩,⟨.covers 139,1,2⟩,⟨.covers 2059,1,4⟩,⟨.covers 163,1,1⟩,⟨.covers 2307,1,4⟩,⟨.covers 1539,1,4⟩,⟨.covers 269,1,6⟩,⟨.covers 3077,1,9⟩,⟨.covers 329,1,4⟩,⟨.covers 777,1,1⟩,⟨.covers 2569,1,8⟩,⟨.covers 3081,1,4⟩,⟨.covers 78,1,1⟩,⟨.covers 526,1,4⟩,⟨.covers 198,1,7⟩,⟨.covers 1094,1,2⟩,⟨.covers 774,1,3⟩,⟨.covers 2566,1,8⟩,⟨.covers 3078,1,3⟩,⟨.covers 1074,1,4⟩,⟨.covers 210,1,2⟩,⟨.covers 450,1,1⟩,⟨.covers 2818,1,14⟩,⟨.covers 3586,1,13⟩,⟨.covers 284,1,3⟩,⟨.covers 2316,1,10⟩,⟨.covers 1548,1,3⟩,⟨.covers 2572,1,9⟩,⟨.covers 116,1,2⟩,⟨.covers 180,1,4⟩,⟨.covers 228,1,6⟩,⟨.covers 2820,1,17⟩,⟨.covers 3588,1,7⟩,⟨.covers 216,1,3⟩,⟨.covers 1560,1,2⟩,⟨.covers 2160,1,4⟩,⟨.covers 1200,1,2⟩,⟨.covers 2224,1,5⟩,⟨.covers 2352,1,4⟩,⟨.covers 1584,1,3⟩,⟨.covers 720,1,1⟩,⟨.covers 912,1,4⟩,⟨.covers 2704,1,9⟩,⟨.covers 3216,1,10⟩,⟨.covers 2272,1,3⟩,⟨.covers 864,1,5⟩,⟨.covers 2656,1,11⟩,⟨.covers 3168,1,4⟩,⟨.covers 1696,1,1⟩,⟨.covers 2496,1,3⟩,⟨.covers 1728,1,2⟩,⟨.covers 1920,1,1⟩,⟨.incident 2,8,-2⟩,⟨.incident 9,8,-4⟩,⟨.incident 11,8,-7⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source27.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source27.rootCodes link27 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual27_025
namespace C13.Global.FastDual27_026
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,10,11]
def points : Finset C13.Point := {2,7,10,11}
def columns : List Code := [379,439,631,635,637,638,699,731,747,823,827,829,830,859,875,883,885,886,889,890,892,923,939,947,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1595,1627,1639,1646,1651,1654,1658,1691,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2619,2647,2653,2667,2675,2677,2681,2731,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3187,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 1031,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3332,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source27.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source27.rootCodes link27 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual27_026
namespace C13.Global.FastDual27_027
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,7,10,11]
def points : Finset C13.Point := {6,7,10,11}
def columns : List Code := [127,191,223,239,319,351,367,379,415,431,439,463,575,607,623,631,671,687,699,719,799,815,823,827,829,830,847,855,859,871,875,883,911,919,923,935,939,947,967,971,979,995,1087,1119,1135,1150,1183,1199,1213,1231,1311,1327,1335,1339,1359,1371,1374,1390,1402,1423,1437,1447,1453,1461,1567,1583,1591,1595,1615,1630,1639,1646,1654,1679,1691,1693,1709,1721,1807,1819,1831,1843,1870,1882,1894,1906,1933,1945,1957,1969,2111,2143,2159,2173,2207,2223,2238,2255,2335,2351,2359,2363,2383,2397,2411,2413,2425,2447,2455,2462,2478,2486,2591,2607,2615,2619,2639,2647,2653,2669,2677,2703,2718,2731,2734,2746,2831,2839,2859,2867,2893,2901,2921,2929,2958,2966,2986,2994,3103,3119,3127,3131,3151,3215,3277,3278,3292,3308,3343,3379,3532,3599,3635,3788]
def rows : List LinearRow := [⟨.covers 519,1,1⟩,⟨.covers 267,1,5⟩,⟨.covers 523,1,3⟩,⟨.covers 149,1,6⟩,⟨.covers 101,1,3⟩,⟨.covers 1061,1,2⟩,⟨.covers 197,1,7⟩,⟨.covers 2117,1,3⟩,⟨.covers 389,1,3⟩,⟨.covers 1157,1,1⟩,⟨.covers 3077,1,7⟩,⟨.covers 169,1,1⟩,⟨.covers 2089,1,3⟩,⟨.covers 329,1,3⟩,⟨.covers 649,1,1⟩,⟨.covers 86,1,6⟩,⟨.covers 2070,1,3⟩,⟨.covers 166,1,5⟩,⟨.covers 582,1,4⟩,⟨.covers 390,1,1⟩,⟨.covers 3078,1,7⟩,⟨.covers 1050,1,1⟩,⟨.covers 106,1,3⟩,⟨.covers 330,1,1⟩,⟨.covers 650,1,3⟩,⟨.covers 2186,1,2⟩,⟨.covers 284,1,5⟩,⟨.covers 540,1,5⟩,⟨.covers 300,1,5⟩,⟨.covers 556,1,5⟩,⟨.covers 116,1,5⟩,⟨.covers 180,1,1⟩,⟨.covers 2820,1,5⟩,⟨.covers 120,1,2⟩,⟨.covers 184,1,6⟩,⟨.covers 1800,1,10⟩,⟨.covers 2824,1,5⟩,⟨.covers 1136,1,1⟩,⟨.covers 2160,1,3⟩,⟨.covers 1200,1,2⟩,⟨.covers 2224,1,2⟩,⟨.covers 720,1,19⟩,⟨.covers 1232,1,19⟩,⟨.covers 2384,1,8⟩,⟨.covers 1616,1,3⟩,⟨.covers 1424,1,4⟩,⟨.covers 2704,1,7⟩,⟨.covers 3344,1,19⟩,⟨.covers 3600,1,19⟩,⟨.covers 736,1,19⟩,⟨.covers 1248,1,19⟩,⟨.covers 1376,1,10⟩,⟨.covers 2656,1,5⟩,⟨.covers 2464,1,7⟩,⟨.covers 1696,1,9⟩,⟨.covers 1472,1,19⟩,⟨.covers 1728,1,19⟩,⟨.covers 1856,1,4⟩,⟨.covers 2880,1,3⟩,⟨.covers 1920,1,4⟩,⟨.covers 2944,1,3⟩]
def bound : Int := 20

theorem column_mask : listMask columns = restrictMask universeMask Source27.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source27.rootCodes link27 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual27_027
