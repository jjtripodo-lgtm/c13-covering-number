import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source02
namespace C13.Global.FastDual02_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,7,8,9]
def points : Finset C13.Point := {6,7,8,9}
def columns : List Code := [127,191,223,239,319,351,367,379,415,431,439,463,575,607,623,631,671,687,699,719,799,815,829,830,847,911,967,971,979,995,1087,1119,1135,1150,1183,1199,1213,1231,1311,1327,1341,1342,1359,1371,1374,1387,1402,1423,1431,1447,1453,1461,1567,1583,1597,1598,1615,1623,1639,1646,1654,1679,1691,1693,1707,1721,1807,1852,1987,2111,2143,2159,2173,2207,2223,2238,2255,2335,2351,2365,2366,2383,2395,2411,2413,2425,2447,2455,2462,2471,2486,2591,2607,2621,2622,2639,2647,2653,2663,2677,2703,2715,2731,2734,2746,2831,2876,3011,3103,3119,3127,3131,3133,3134,3151,3165,3166,3181,3182,3196,3215,3229,3230,3245,3246,3260,3277,3278,3292,3308,3343,3358,3373,3388,3403,3418,3433,3448,3463,3478,3493,3508,3599,3613,3630,3644,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 1043,1,5⟩,⟨.covers 2067,1,5⟩,⟨.covers 1059,1,5⟩,⟨.covers 2083,1,5⟩,⟨.covers 2061,1,5⟩,⟨.covers 149,1,4⟩,⟨.covers 101,1,7⟩,⟨.covers 293,1,1⟩,⟨.covers 197,1,7⟩,⟨.covers 581,1,2⟩,⟨.covers 389,1,4⟩,⟨.covers 1157,1,2⟩,⟨.covers 89,1,5⟩,⟨.covers 537,1,1⟩,⟨.covers 169,1,5⟩,⟨.covers 297,1,2⟩,⟨.covers 2121,1,3⟩,⟨.covers 649,1,1⟩,⟨.covers 1161,1,3⟩,⟨.covers 777,1,11⟩,⟨.covers 1289,1,2⟩,⟨.covers 2577,1,4⟩,⟨.covers 1313,1,1⟩,⟨.covers 2337,1,1⟩,⟨.covers 1038,1,5⟩,⟨.covers 86,1,3⟩,⟨.covers 278,1,4⟩,⟨.covers 550,1,2⟩,⟨.covers 1094,1,3⟩,⟨.covers 2182,1,2⟩,⟨.covers 2566,1,4⟩,⟨.covers 154,1,1⟩,⟨.covers 282,1,3⟩,⟨.covers 554,1,3⟩,⟨.covers 330,1,3⟩,⟨.covers 2186,1,3⟩,⟨.covers 1546,1,2⟩,⟨.covers 3330,1,8⟩,⟨.covers 3586,1,5⟩,⟨.covers 180,1,6⟩,⟨.covers 368,1,7⟩,⟨.covers 624,1,5⟩,⟨.covers 432,1,1⟩,⟨.covers 688,1,8⟩,⟨.covers 464,1,20⟩,⟨.covers 1232,1,20⟩,⟨.covers 2384,1,2⟩,⟨.covers 1616,1,7⟩,⟨.covers 1424,1,1⟩,⟨.covers 2704,1,4⟩,⟨.covers 1808,1,20⟩,⟨.covers 2832,1,20⟩,⟨.covers 480,1,20⟩,⟨.covers 1248,1,20⟩,⟨.covers 1376,1,7⟩,⟨.covers 2464,1,7⟩,⟨.covers 1696,1,1⟩,⟨.covers 1472,1,20⟩,⟨.covers 2496,1,20⟩,⟨.covers 3392,1,4⟩,⟨.covers 3648,1,6⟩,⟨.covers 3456,1,4⟩,⟨.covers 3712,1,6⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source02.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source02.rootCodes link02 points rows bound = true := by decide +kernel

end C13.Global.FastDual02_008
namespace C13.Global.FastDual02_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,7,10,11]
def points : Finset C13.Point := {6,7,10,11}
def columns : List Code := [127,191,223,239,319,351,367,379,415,431,439,463,575,607,623,631,671,687,699,719,799,815,823,827,829,830,847,855,859,871,875,883,911,919,923,935,939,947,967,971,979,995,1087,1119,1135,1150,1183,1199,1213,1231,1311,1327,1335,1339,1359,1371,1374,1390,1402,1423,1437,1447,1453,1461,1567,1583,1591,1595,1615,1630,1639,1646,1654,1679,1691,1693,1709,1721,1807,1819,1831,1843,1870,1882,1894,1906,1933,1945,1957,1969,2111,2143,2159,2173,2207,2223,2238,2255,2335,2351,2359,2363,2383,2397,2411,2413,2425,2447,2455,2462,2478,2486,2591,2607,2615,2619,2639,2647,2653,2669,2677,2703,2718,2731,2734,2746,2831,2839,2859,2867,2893,2901,2921,2929,2958,2966,2986,2994,3103,3119,3127,3131,3151,3215,3277,3278,3292,3308,3343,3379,3532,3599,3635,3788]
def rows : List LinearRow := [⟨.covers 149,1,1⟩,⟨.covers 101,1,1⟩,⟨.covers 197,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 540,1,1⟩,⟨.covers 300,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 464,1,2⟩,⟨.covers 1232,1,2⟩,⟨.covers 2384,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 3344,1,2⟩,⟨.covers 3600,1,2⟩,⟨.covers 480,1,2⟩,⟨.covers 1248,1,2⟩,⟨.covers 1376,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 1472,1,2⟩,⟨.covers 1728,1,2⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source02.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source02.rootCodes link02 points rows bound = true := by decide +kernel

end C13.Global.FastDual02_009
namespace C13.Global.FastDual02_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [8,9,10,11]
def points : Finset C13.Point := {8,9,10,11}
def columns : List Code := [127,191,223,239,247,251,253,254,319,351,367,379,381,382,415,431,439,445,446,463,471,475,478,487,491,493,499,501,502,505,506,508,575,607,623,631,637,638,671,687,699,701,702,719,727,731,733,743,747,750,755,757,758,761,762,764,799,815,829,830,847,892,911,956,967,971,979,995,1009,1010,1012,1016,1087,1119,1135,1143,1147,1150,1183,1199,1207,1211,1213,1231,1243,1245,1246,1255,1261,1262,1267,1269,1270,1273,1274,1276,1311,1327,1359,1371,1374,1402,1423,1447,1453,1461,1498,1509,1521,1522,1524,1528,1567,1583,1615,1639,1646,1654,1679,1691,1693,1721,1753,1766,1777,1778,1780,1784,1807,2032,2111,2143,2159,2167,2171,2173,2207,2223,2231,2235,2238,2255,2263,2269,2270,2283,2285,2286,2291,2293,2294,2297,2298,2300,2335,2351,2383,2411,2413,2425,2447,2455,2462,2486,2518,2537,2545,2546,2548,2552,2591,2607,2639,2647,2653,2677,2703,2731,2734,2746,2773,2794,2801,2802,2804,2808,2831,3056,3103,3119,3127,3131,3151,3187,3215,3251,3277,3278,3292,3308,3313,3314,3316,3320,3343,3568,3599,3824]
def rows : List LinearRow := [⟨.covers 3089,1,1⟩,⟨.covers 1313,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 1604,1,1⟩,⟨.covers 1304,1,1⟩,⟨.covers 1560,1,1⟩,⟨.covers 3208,1,1⟩,⟨.covers 1808,1,1⟩,⟨.covers 3344,1,1⟩,⟨.covers 3600,1,1⟩,⟨.incident 10,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source02.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source02.rootCodes link02 points rows bound = true := by decide +kernel

end C13.Global.FastDual02_010
