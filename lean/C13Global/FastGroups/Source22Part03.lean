import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source22
namespace C13.Global.FastDual22_024
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,11]
def points : Finset C13.Point := {3,7,9,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,829,830,855,871,885,886,892,967,979,995,1143,1245,1335,1367,1371,1373,1374,1383,1395,1397,1398,1401,1402,1404,1431,1447,1461,1479,1493,1509,1623,1639,1653,1654,1691,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2647,2677,2731,2734,2746,2794,2901,2986,3127,3159,3187,3189,3277,3278,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 519,1,5⟩,⟨.covers 2055,1,5⟩,⟨.covers 75,1,3⟩,⟨.covers 1035,1,8⟩,⟨.covers 1059,1,3⟩,⟨.covers 2307,1,5⟩,⟨.covers 2061,1,8⟩,⟨.covers 777,1,11⟩,⟨.covers 2569,1,11⟩,⟨.covers 3081,1,3⟩,⟨.covers 1038,1,11⟩,⟨.covers 1062,1,3⟩,⟨.covers 774,1,5⟩,⟨.covers 778,1,5⟩,⟨.covers 1546,1,3⟩,⟨.covers 210,1,11⟩,⟨.covers 2818,1,5⟩,⟨.covers 3586,1,5⟩,⟨.covers 156,1,11⟩,⟨.covers 108,1,3⟩,⟨.covers 2572,1,11⟩,⟨.covers 180,1,11⟩,⟨.covers 120,1,8⟩,⟨.covers 184,1,3⟩,⟨.covers 2160,1,3⟩,⟨.covers 1584,1,8⟩,⟨.covers 2608,1,8⟩,⟨.covers 2832,1,11⟩,⟨.covers 3600,1,11⟩,⟨.covers 480,1,11⟩,⟨.covers 3168,1,5⟩,⟨.covers 3232,1,3⟩,⟨.covers 1824,1,3⟩,⟨.covers 3360,1,3⟩,⟨.covers 1728,1,11⟩,⟨.covers 2752,1,11⟩,⟨.covers 3456,1,11⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_024
namespace C13.Global.FastDual22_025
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,7,8,9]
def points : Finset C13.Point := {6,7,8,9}
def columns : List Code := [127,191,223,239,319,351,367,379,415,431,439,463,575,607,623,631,671,687,699,719,799,815,829,830,847,911,967,971,979,995,1087,1119,1135,1150,1183,1199,1213,1231,1311,1327,1341,1342,1359,1371,1374,1387,1402,1423,1431,1447,1453,1461,1567,1583,1597,1598,1615,1623,1639,1646,1654,1679,1691,1693,1707,1721,1807,1852,1987,2111,2143,2159,2173,2207,2223,2238,2255,2335,2351,2365,2366,2383,2395,2411,2413,2425,2447,2455,2462,2471,2486,2591,2607,2621,2622,2639,2647,2653,2663,2677,2703,2715,2731,2734,2746,2831,2876,3011,3103,3119,3127,3131,3133,3134,3151,3165,3166,3181,3182,3196,3215,3229,3230,3245,3246,3260,3277,3278,3292,3308,3343,3358,3373,3388,3403,3418,3433,3448,3463,3478,3493,3508,3599,3613,3630,3644,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 1043,1,4⟩,⟨.covers 2067,1,4⟩,⟨.covers 1059,1,4⟩,⟨.covers 2083,1,4⟩,⟨.covers 1037,1,2⟩,⟨.covers 2061,1,2⟩,⟨.covers 149,1,6⟩,⟨.covers 533,1,2⟩,⟨.covers 101,1,6⟩,⟨.covers 293,1,2⟩,⟨.covers 581,1,2⟩,⟨.covers 2117,1,2⟩,⟨.covers 389,1,2⟩,⟨.covers 1157,1,2⟩,⟨.covers 89,1,6⟩,⟨.covers 537,1,2⟩,⟨.covers 169,1,6⟩,⟨.covers 297,1,2⟩,⟨.covers 201,1,8⟩,⟨.covers 329,1,2⟩,⟨.covers 2121,1,2⟩,⟨.covers 649,1,2⟩,⟨.covers 1161,1,2⟩,⟨.covers 1038,1,2⟩,⟨.covers 2062,1,2⟩,⟨.covers 1094,1,2⟩,⟨.covers 2182,1,2⟩,⟨.covers 774,1,4⟩,⟨.covers 1098,1,2⟩,⟨.covers 2186,1,2⟩,⟨.covers 778,1,8⟩,⟨.covers 114,1,6⟩,⟨.covers 178,1,6⟩,⟨.covers 3330,1,8⟩,⟨.covers 3586,1,8⟩,⟨.covers 368,1,2⟩,⟨.covers 624,1,2⟩,⟨.covers 432,1,2⟩,⟨.covers 688,1,2⟩,⟨.covers 464,1,21⟩,⟨.covers 2256,1,21⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,8⟩,⟨.covers 1424,1,4⟩,⟨.covers 2704,1,8⟩,⟨.covers 1808,1,17⟩,⟨.covers 2832,1,17⟩,⟨.covers 480,1,21⟩,⟨.covers 2272,1,21⟩,⟨.covers 1376,1,8⟩,⟨.covers 2656,1,4⟩,⟨.covers 2464,1,8⟩,⟨.covers 1696,1,4⟩,⟨.covers 1472,1,21⟩,⟨.covers 2496,1,21⟩,⟨.covers 3392,1,4⟩,⟨.covers 3648,1,4⟩,⟨.covers 3456,1,4⟩,⟨.covers 3712,1,4⟩,⟨.incident 6,8,-2⟩,⟨.incident 7,8,-2⟩]
def bound : Int := 17

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_025
namespace C13.Global.FastDual22_026
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,8,9,11]
def points : Finset C13.Point := {6,8,9,11}
def columns : List Code := [127,191,223,239,254,319,351,367,379,415,431,439,445,446,463,475,491,506,575,607,623,631,671,687,699,701,702,719,727,743,758,799,815,829,830,847,911,956,967,971,979,995,1010,1087,1119,1135,1150,1183,1199,1207,1211,1213,1214,1231,1246,1262,1311,1327,1341,1342,1359,1371,1374,1387,1402,1423,1431,1438,1447,1453,1461,1462,1468,1483,1498,1567,1583,1597,1598,1615,1623,1639,1646,1654,1679,1691,1693,1707,1710,1721,1722,1724,1735,1766,1807,1852,1987,2111,2143,2159,2173,2207,2223,2231,2235,2238,2255,2269,2285,2300,2335,2351,2383,2411,2413,2425,2447,2455,2462,2486,2537,2552,2591,2607,2639,2647,2653,2677,2703,2731,2734,2746,2773,2804,2831,3056,3103,3119,3127,3131,3151,3165,3181,3215,3223,3230,3243,3246,3251,3254,3258,3277,3278,3292,3308,3343,3433,3478,3599,3669,3754]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 135,1,1⟩,⟨.covers 1031,1,3⟩,⟨.covers 75,1,6⟩,⟨.covers 139,1,1⟩,⟨.covers 1035,1,3⟩,⟨.covers 83,1,13⟩,⟨.covers 147,1,1⟩,⟨.covers 2067,1,12⟩,⟨.covers 99,1,13⟩,⟨.covers 163,1,1⟩,⟨.covers 2083,1,12⟩,⟨.covers 77,1,9⟩,⟨.covers 1037,1,1⟩,⟨.covers 149,1,4⟩,⟨.covers 101,1,4⟩,⟨.covers 293,1,18⟩,⟨.covers 197,1,9⟩,⟨.covers 389,1,16⟩,⟨.covers 89,1,4⟩,⟨.covers 537,1,18⟩,⟨.covers 169,1,4⟩,⟨.covers 201,1,9⟩,⟨.covers 649,1,16⟩,⟨.covers 2097,1,16⟩,⟨.covers 657,1,6⟩,⟨.covers 417,1,6⟩,⟨.covers 142,1,3⟩,⟨.covers 1038,1,25⟩,⟨.covers 550,1,17⟩,⟨.covers 282,1,17⟩,⟨.covers 1074,1,6⟩,⟨.covers 2098,1,17⟩,⟨.covers 210,1,11⟩,⟨.covers 1106,1,8⟩,⟨.covers 226,1,11⟩,⟨.covers 1122,1,8⟩,⟨.covers 1794,1,4⟩,⟨.covers 2818,1,4⟩,⟨.covers 3586,1,3⟩,⟨.covers 2188,1,14⟩,⟨.covers 116,1,10⟩,⟨.covers 180,1,1⟩,⟨.covers 212,1,11⟩,⟨.covers 1124,1,12⟩,⟨.covers 420,1,17⟩,⟨.covers 1188,1,5⟩,⟨.covers 1220,1,9⟩,⟨.covers 2244,1,1⟩,⟨.covers 120,1,10⟩,⟨.covers 184,1,1⟩,⟨.covers 1112,1,12⟩,⟨.covers 664,1,17⟩,⟨.covers 1176,1,5⟩,⟨.covers 232,1,11⟩,⟨.covers 1224,1,9⟩,⟨.covers 2248,1,1⟩,⟨.covers 3336,1,3⟩,⟨.covers 1616,1,1⟩,⟨.covers 1808,1,36⟩,⟨.covers 3344,1,35⟩,⟨.covers 3600,1,30⟩,⟨.covers 3360,1,27⟩,⟨.covers 3616,1,32⟩,⟨.covers 1856,1,27⟩,⟨.incident 6,8,4⟩,⟨.incident 8,8,31⟩,⟨.incident 9,8,31⟩,⟨.incident 11,8,32⟩]
def bound : Int := 99

theorem column_mask : listMask columns = restrictMask universeMask Source22.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source22.rootCodes link22 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual22_026
