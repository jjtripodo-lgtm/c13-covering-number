import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source24
namespace C13.Global.FastDual24_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,9,11]
def points : Finset C13.Point := {3,7,9,11}
def columns : List Code := [253,375,379,381,382,439,471,487,501,631,699,761,829,830,855,871,885,886,892,967,979,995,1009,1143,1245,1335,1367,1371,1373,1374,1383,1395,1397,1398,1401,1402,1404,1431,1447,1461,1479,1493,1509,1623,1639,1653,1654,1691,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2167,2286,2300,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2548,2647,2677,2731,2734,2746,2794,2808,2901,2986,3056,3127,3159,3187,3189,3277,3278,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 519,1,1⟩,⟨.covers 2055,1,1⟩,⟨.covers 75,1,2⟩,⟨.covers 147,1,1⟩,⟨.covers 525,1,2⟩,⟨.covers 2061,1,2⟩,⟨.covers 2569,1,2⟩,⟨.covers 1185,1,1⟩,⟨.covers 270,1,2⟩,⟨.covers 198,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 2098,1,1⟩,⟨.covers 610,1,1⟩,⟨.covers 2818,1,2⟩,⟨.covers 3586,1,1⟩,⟨.covers 2572,1,2⟩,⟨.covers 420,1,1⟩,⟨.covers 216,1,2⟩,⟨.covers 1584,1,1⟩,⟨.covers 2832,1,2⟩,⟨.covers 3600,1,2⟩,⟨.covers 3168,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 1824,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 1920,1,2⟩,⟨.covers 3456,1,2⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source24.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source24.rootCodes link24 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual24_008
namespace C13.Global.FastDual24_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,7,8,9]
def points : Finset C13.Point := {6,7,8,9}
def columns : List Code := [127,191,223,239,319,351,367,379,415,431,439,463,575,607,623,631,671,687,699,719,799,815,829,830,847,911,967,971,979,995,1087,1119,1135,1150,1183,1199,1213,1231,1311,1327,1341,1342,1359,1371,1374,1387,1402,1423,1431,1447,1453,1461,1567,1583,1597,1598,1615,1623,1639,1646,1654,1679,1691,1693,1707,1721,1807,1852,1987,2111,2143,2159,2173,2207,2223,2238,2255,2335,2351,2365,2366,2383,2395,2411,2413,2425,2447,2455,2462,2471,2486,2591,2607,2621,2622,2639,2647,2653,2663,2677,2703,2715,2731,2734,2746,2831,2876,3011,3103,3119,3127,3131,3133,3134,3151,3165,3166,3181,3182,3196,3215,3229,3230,3245,3246,3260,3277,3278,3292,3308,3343,3358,3373,3388,3403,3418,3433,3448,3463,3478,3493,3508,3599,3613,3630,3644,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 89,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 368,1,1⟩,⟨.covers 624,1,1⟩,⟨.covers 432,1,1⟩,⟨.covers 688,1,1⟩,⟨.covers 464,1,2⟩,⟨.covers 2256,1,2⟩,⟨.covers 1616,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 1808,1,2⟩,⟨.covers 2832,1,2⟩,⟨.covers 480,1,2⟩,⟨.covers 2272,1,2⟩,⟨.covers 1376,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 1472,1,2⟩,⟨.covers 2496,1,2⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source24.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source24.rootCodes link24 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual24_009
namespace C13.Global.FastDual24_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [7,8,9,11]
def points : Finset C13.Point := {7,8,9,11}
def columns : List Code := [127,191,223,239,253,319,351,367,379,381,382,415,431,439,463,471,487,501,575,607,623,631,637,638,671,687,699,719,731,747,761,799,815,829,830,847,892,911,967,971,979,995,1009,1087,1119,1135,1143,1147,1149,1150,1183,1199,1213,1231,1245,1261,1311,1327,1341,1342,1359,1371,1374,1387,1389,1401,1402,1404,1423,1431,1447,1453,1461,1479,1509,1567,1583,1597,1598,1615,1623,1629,1639,1646,1653,1654,1660,1679,1691,1693,1707,1721,1739,1753,1807,1852,1987,2111,2143,2159,2167,2171,2173,2207,2223,2238,2255,2270,2286,2300,2335,2351,2383,2411,2413,2425,2447,2455,2462,2486,2518,2548,2591,2607,2639,2647,2653,2677,2703,2731,2734,2746,2794,2808,2831,3056,3103,3119,3127,3131,3151,3159,3165,3179,3181,3187,3189,3193,3215,3230,3246,3277,3278,3292,3308,3343,3433,3478,3599,3669,3754]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 135,1,6⟩,⟨.covers 1031,1,3⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,6⟩,⟨.covers 1035,1,3⟩,⟨.covers 83,1,1⟩,⟨.covers 147,1,13⟩,⟨.covers 2067,1,12⟩,⟨.covers 99,1,1⟩,⟨.covers 163,1,13⟩,⟨.covers 2083,1,12⟩,⟨.covers 77,1,3⟩,⟨.covers 1037,1,25⟩,⟨.covers 293,1,17⟩,⟨.covers 537,1,17⟩,⟨.covers 1073,1,6⟩,⟨.covers 2097,1,17⟩,⟨.covers 209,1,11⟩,⟨.covers 1169,1,9⟩,⟨.covers 225,1,11⟩,⟨.covers 1185,1,8⟩,⟨.covers 142,1,9⟩,⟨.covers 1038,1,1⟩,⟨.covers 86,1,4⟩,⟨.covers 166,1,4⟩,⟨.covers 550,1,18⟩,⟨.covers 198,1,9⟩,⟨.covers 582,1,16⟩,⟨.covers 154,1,4⟩,⟨.covers 282,1,18⟩,⟨.covers 106,1,4⟩,⟨.covers 202,1,9⟩,⟨.covers 330,1,16⟩,⟨.covers 2098,1,16⟩,⟨.covers 338,1,6⟩,⟨.covers 610,1,6⟩,⟨.covers 1794,1,4⟩,⟨.covers 2818,1,4⟩,⟨.covers 3586,1,3⟩,⟨.covers 2124,1,14⟩,⟨.covers 116,1,1⟩,⟨.covers 180,1,10⟩,⟨.covers 212,1,11⟩,⟨.covers 612,1,17⟩,⟨.covers 1124,1,5⟩,⟨.covers 1188,1,12⟩,⟨.covers 1220,1,9⟩,⟨.covers 2244,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 184,1,10⟩,⟨.covers 344,1,17⟩,⟨.covers 1112,1,5⟩,⟨.covers 1176,1,12⟩,⟨.covers 232,1,11⟩,⟨.covers 1224,1,9⟩,⟨.covers 2248,1,1⟩,⟨.covers 3336,1,3⟩,⟨.covers 3216,1,1⟩,⟨.covers 1808,1,36⟩,⟨.covers 3344,1,30⟩,⟨.covers 3600,1,35⟩,⟨.covers 1696,1,1⟩,⟨.covers 3360,1,32⟩,⟨.covers 3616,1,27⟩,⟨.covers 1856,1,27⟩,⟨.incident 7,8,4⟩,⟨.incident 8,8,31⟩,⟨.incident 9,8,31⟩,⟨.incident 11,8,32⟩]
def bound : Int := 99

theorem column_mask : listMask columns = restrictMask universeMask Source24.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source24.rootCodes link24 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual24_010
