import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source53
namespace C13.Global.FastDual53_024
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,10]
def points : Finset C13.Point := {2,7,9,10}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1639,1646,1654,1691,1721,1753,1894,1945,2171,2270,2363,2395,2411,2419,2425,2426,2455,2462,2486,2518,2647,2653,2677,2678,2684,2715,2731,2746,2763,2794,2845,2876,2901,2932,2955,2986,3011,3042,3131,3163,3187,3194,3277,3278,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 1031,1,5⟩,⟨.covers 2055,1,3⟩,⟨.covers 1035,1,5⟩,⟨.covers 163,1,2⟩,⟨.covers 2083,1,1⟩,⟨.covers 1283,1,5⟩,⟨.covers 1539,1,13⟩,⟨.covers 2563,1,2⟩,⟨.covers 45,1,1⟩,⟨.covers 525,1,3⟩,⟨.covers 53,1,1⟩,⟨.covers 197,1,12⟩,⟨.covers 773,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 2097,1,2⟩,⟨.covers 2625,1,1⟩,⟨.covers 46,1,2⟩,⟨.covers 142,1,3⟩,⟨.covers 1286,1,2⟩,⟨.covers 3078,1,6⟩,⟨.covers 330,1,2⟩,⟨.covers 778,1,4⟩,⟨.covers 3082,1,5⟩,⟨.covers 226,1,3⟩,⟨.covers 1794,1,15⟩,⟨.covers 3586,1,12⟩,⟨.covers 300,1,1⟩,⟨.covers 1292,1,11⟩,⟨.covers 1548,1,15⟩,⟨.covers 2572,1,3⟩,⟨.covers 344,1,1⟩,⟨.covers 2216,1,1⟩,⟨.covers 1352,1,1⟩,⟨.covers 1800,1,16⟩,⟨.covers 2824,1,1⟩,⟨.covers 3592,1,17⟩,⟨.covers 1136,1,5⟩,⟨.covers 2224,1,3⟩,⟨.covers 1328,1,5⟩,⟨.covers 1584,1,5⟩,⟨.covers 2608,1,2⟩,⟨.covers 1232,1,9⟩,⟨.covers 848,1,5⟩,⟨.covers 1616,1,8⟩,⟨.covers 3152,1,5⟩,⟨.covers 912,1,1⟩,⟨.covers 928,1,1⟩,⟨.covers 1696,1,13⟩,⟨.covers 3232,1,12⟩,⟨.covers 1472,1,1⟩,⟨.covers 2752,1,3⟩,⟨.incident 9,8,-4⟩,⟨.incident 10,8,-10⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_024
namespace C13.Global.FastDual53_025
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,11]
def points : Finset C13.Point := {2,7,9,11}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1387,1395,1401,1402,1447,1453,1461,1509,1639,1646,1653,1654,1660,1691,1707,1721,1739,1753,1838,1852,1894,1908,1931,1945,1987,2001,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2647,2653,2677,2731,2746,2794,2901,2986,3131,3179,3187,3193,3277,3278,3292,3308,3371,3379,3433,3441,3470,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 1031,1,3⟩,⟨.covers 2059,1,5⟩,⟨.covers 147,1,1⟩,⟨.covers 1043,1,3⟩,⟨.covers 2307,1,5⟩,⟨.covers 1539,1,2⟩,⟨.covers 773,1,2⟩,⟨.covers 2309,1,9⟩,⟨.covers 777,1,4⟩,⟨.covers 3081,1,5⟩,⟨.covers 46,1,3⟩,⟨.covers 54,1,2⟩,⟨.covers 198,1,2⟩,⟨.covers 774,1,1⟩,⟨.covers 2566,1,18⟩,⟨.covers 3078,1,12⟩,⟨.covers 3090,1,2⟩,⟨.covers 450,1,2⟩,⟨.covers 1602,1,2⟩,⟨.covers 2818,1,9⟩,⟨.covers 3586,1,18⟩,⟨.covers 156,1,12⟩,⟨.covers 172,1,3⟩,⟨.covers 2316,1,2⟩,⟨.covers 1548,1,2⟩,⟨.covers 2572,1,18⟩,⟨.covers 2820,1,7⟩,⟨.covers 3588,1,18⟩,⟨.covers 1560,1,1⟩,⟨.covers 360,1,3⟩,⟨.covers 2376,1,2⟩,⟨.covers 2160,1,5⟩,⟨.covers 1200,1,3⟩,⟨.covers 2352,1,5⟩,⟨.covers 1584,1,3⟩,⟨.covers 720,1,3⟩,⟨.covers 1232,1,2⟩,⟨.covers 912,1,1⟩,⟨.covers 2704,1,18⟩,⟨.covers 864,1,3⟩,⟨.covers 2656,1,13⟩,⟨.covers 3168,1,5⟩,⟨.covers 928,1,1⟩,⟨.covers 2464,1,7⟩,⟨.covers 2496,1,10⟩,⟨.covers 1728,1,1⟩,⟨.covers 2752,1,5⟩,⟨.incident 9,8,-4⟩,⟨.incident 11,8,-11⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_025
namespace C13.Global.FastDual53_026
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,10,11]
def points : Finset C13.Point := {2,7,10,11}
def columns : List Code := [379,439,631,635,637,638,699,731,747,823,827,829,830,859,875,883,885,886,889,890,892,923,939,947,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1595,1627,1639,1646,1651,1654,1658,1691,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2619,2647,2653,2667,2675,2677,2681,2731,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3187,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 1031,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 86,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 300,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_026
namespace C13.Global.FastDual53_027
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,7,10,11]
def points : Finset C13.Point := {6,7,10,11}
def columns : List Code := [127,191,223,239,319,351,367,379,415,431,439,463,575,607,623,631,671,687,699,719,799,815,823,827,829,830,847,855,859,871,875,883,911,919,923,935,939,947,967,971,979,995,1087,1119,1135,1150,1183,1199,1213,1231,1311,1327,1335,1339,1359,1371,1374,1390,1402,1423,1437,1447,1453,1461,1567,1583,1591,1595,1615,1630,1639,1646,1654,1679,1691,1693,1709,1721,1807,1819,1831,1843,1870,1882,1894,1906,1933,1945,1957,1969,2111,2143,2159,2173,2207,2223,2238,2255,2335,2351,2359,2363,2383,2397,2411,2413,2425,2447,2455,2462,2478,2486,2591,2607,2615,2619,2639,2647,2653,2669,2677,2703,2718,2731,2734,2746,2831,2839,2859,2867,2893,2901,2921,2929,2958,2966,2986,2994,3103,3119,3127,3131,3151,3215,3277,3278,3292,3308,3343,3379,3532,3599,3635,3788]
def rows : List LinearRow := [⟨.covers 3077,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 540,1,1⟩,⟨.covers 300,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 720,1,2⟩,⟨.covers 1232,1,2⟩,⟨.covers 2384,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 3344,1,2⟩,⟨.covers 3600,1,2⟩,⟨.covers 736,1,2⟩,⟨.covers 1248,1,2⟩,⟨.covers 1376,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 1472,1,2⟩,⟨.covers 1728,1,2⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_027
