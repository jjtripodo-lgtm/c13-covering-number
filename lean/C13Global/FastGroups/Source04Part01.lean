import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source04
namespace C13.Global.FastDual04_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,10]
def points : Finset C13.Point := {2,7,9,10}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1639,1646,1654,1691,1721,1753,1894,1945,2171,2270,2363,2395,2411,2419,2425,2426,2455,2462,2486,2518,2647,2653,2677,2678,2684,2715,2731,2746,2763,2794,2845,2876,2901,2932,2955,2986,3011,3042,3131,3163,3187,3194,3277,3278,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 1031,1,5⟩,⟨.covers 2055,1,3⟩,⟨.covers 139,1,2⟩,⟨.covers 1035,1,4⟩,⟨.covers 1283,1,4⟩,⟨.covers 1539,1,8⟩,⟨.covers 2563,1,5⟩,⟨.covers 77,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 525,1,4⟩,⟨.covers 149,1,4⟩,⟨.covers 197,1,11⟩,⟨.covers 2117,1,1⟩,⟨.covers 773,1,4⟩,⟨.covers 1541,1,1⟩,⟨.covers 2097,1,3⟩,⟨.covers 3105,1,1⟩,⟨.covers 449,1,1⟩,⟨.covers 270,1,7⟩,⟨.covers 1038,1,4⟩,⟨.covers 166,1,3⟩,⟨.covers 198,1,3⟩,⟨.covers 202,1,1⟩,⟨.covers 330,1,4⟩,⟨.covers 778,1,1⟩,⟨.covers 3082,1,4⟩,⟨.covers 1794,1,14⟩,⟨.covers 3586,1,14⟩,⟨.covers 92,1,3⟩,⟨.covers 1292,1,12⟩,⟨.covers 1548,1,10⟩,⟨.covers 116,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 2344,1,3⟩,⟨.covers 2600,1,1⟩,⟨.covers 1800,1,14⟩,⟨.covers 3592,1,14⟩,⟨.covers 1136,1,4⟩,⟨.covers 1200,1,4⟩,⟨.covers 2224,1,4⟩,⟨.covers 1328,1,4⟩,⟨.covers 2608,1,4⟩,⟨.covers 464,1,4⟩,⟨.covers 1232,1,5⟩,⟨.covers 848,1,5⟩,⟨.covers 1616,1,9⟩,⟨.covers 3152,1,4⟩,⟨.covers 736,1,6⟩,⟨.covers 928,1,3⟩,⟨.covers 1696,1,10⟩,⟨.covers 3232,1,12⟩,⟨.covers 1472,1,1⟩,⟨.covers 2752,1,1⟩,⟨.incident 9,8,-2⟩,⟨.incident 10,8,-5⟩]
def bound : Int := 8

theorem column_mask : listMask columns = restrictMask universeMask Source04.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source04.rootCodes link04 points rows bound = true := by decide +kernel

end C13.Global.FastDual04_008
namespace C13.Global.FastDual04_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,11]
def points : Finset C13.Point := {2,7,9,11}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1387,1395,1401,1402,1447,1453,1461,1509,1639,1646,1653,1654,1660,1691,1707,1721,1739,1753,1838,1852,1894,1908,1931,1945,1987,2001,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2647,2653,2677,2731,2746,2794,2901,2986,3131,3179,3187,3193,3277,3278,3292,3308,3371,3379,3433,3441,3470,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 135,1,5⟩,⟨.covers 1031,1,3⟩,⟨.covers 139,1,2⟩,⟨.covers 2059,1,4⟩,⟨.covers 2307,1,4⟩,⟨.covers 1539,1,5⟩,⟨.covers 141,1,2⟩,⟨.covers 269,1,6⟩,⟨.covers 2061,1,1⟩,⟨.covers 149,1,3⟩,⟨.covers 197,1,4⟩,⟨.covers 201,1,1⟩,⟨.covers 329,1,4⟩,⟨.covers 777,1,2⟩,⟨.covers 2569,1,7⟩,⟨.covers 3081,1,4⟩,⟨.covers 526,1,6⟩,⟨.covers 774,1,1⟩,⟨.covers 2566,1,13⟩,⟨.covers 3078,1,12⟩,⟨.covers 1074,1,4⟩,⟨.covers 1346,1,3⟩,⟨.covers 2818,1,13⟩,⟨.covers 3586,1,13⟩,⟨.covers 156,1,11⟩,⟨.covers 284,1,2⟩,⟨.covers 108,1,1⟩,⟨.covers 1548,1,2⟩,⟨.covers 2572,1,5⟩,⟨.covers 116,1,2⟩,⟨.covers 2820,1,13⟩,⟨.covers 3588,1,13⟩,⟨.covers 216,1,2⟩,⟨.covers 1304,1,1⟩,⟨.covers 1560,1,2⟩,⟨.covers 2160,1,4⟩,⟨.covers 1200,1,5⟩,⟨.covers 2224,1,8⟩,⟨.covers 2352,1,4⟩,⟨.covers 1584,1,3⟩,⟨.covers 720,1,4⟩,⟨.covers 912,1,4⟩,⟨.covers 2704,1,5⟩,⟨.covers 480,1,4⟩,⟨.covers 2272,1,7⟩,⟨.covers 864,1,4⟩,⟨.covers 3168,1,4⟩,⟨.covers 2496,1,12⟩,⟨.covers 2752,1,6⟩,⟨.incident 9,8,-1⟩,⟨.incident 11,8,-4⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source04.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source04.rootCodes link04 points rows bound = true := by decide +kernel

end C13.Global.FastDual04_009
namespace C13.Global.FastDual04_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,10,11]
def points : Finset C13.Point := {2,7,10,11}
def columns : List Code := [379,439,631,635,637,638,699,731,747,823,827,829,830,859,875,883,885,886,889,890,892,923,939,947,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1595,1627,1639,1646,1651,1654,1658,1691,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2619,2647,2653,2667,2675,2677,2681,2731,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3187,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 3332,1,1⟩,⟨.covers 464,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 480,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 1696,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source04.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source04.rootCodes link04 points rows bound = true := by decide +kernel

end C13.Global.FastDual04_010
namespace C13.Global.FastDual04_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [8,9,10,11]
def points : Finset C13.Point := {8,9,10,11}
def columns : List Code := [127,191,223,239,247,251,253,254,319,351,367,379,381,382,415,431,439,445,446,463,471,475,478,487,491,493,499,501,502,505,506,508,575,607,623,631,637,638,671,687,699,701,702,719,727,731,733,743,747,750,755,757,758,761,762,764,799,815,829,830,847,892,911,956,967,971,979,995,1009,1010,1012,1016,1087,1119,1135,1143,1147,1150,1183,1199,1207,1211,1213,1231,1243,1245,1246,1255,1261,1262,1267,1269,1270,1273,1274,1276,1311,1327,1359,1371,1374,1402,1423,1447,1453,1461,1498,1509,1521,1522,1524,1528,1567,1583,1615,1639,1646,1654,1679,1691,1693,1721,1753,1766,1777,1778,1780,1784,1807,2032,2111,2143,2159,2167,2171,2173,2207,2223,2231,2235,2238,2255,2263,2269,2270,2283,2285,2286,2291,2293,2294,2297,2298,2300,2335,2351,2383,2411,2413,2425,2447,2455,2462,2486,2518,2537,2545,2546,2548,2552,2591,2607,2639,2647,2653,2677,2703,2731,2734,2746,2773,2794,2801,2802,2804,2808,2831,3056,3103,3119,3127,3131,3151,3187,3215,3251,3277,3278,3292,3308,3313,3314,3316,3320,3343,3568,3599,3824]
def rows : List LinearRow := [⟨.covers 3105,1,1⟩,⟨.covers 1346,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 1604,1,1⟩,⟨.covers 1412,1,1⟩,⟨.covers 3144,1,1⟩,⟨.covers 1672,1,1⟩,⟨.covers 1808,1,1⟩,⟨.covers 3344,1,1⟩,⟨.covers 3600,1,1⟩,⟨.incident 10,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source04.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source04.rootCodes link04 points rows bound = true := by decide +kernel

end C13.Global.FastDual04_011
