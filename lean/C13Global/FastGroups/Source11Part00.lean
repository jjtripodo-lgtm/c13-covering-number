import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source11
namespace C13.Global.FastDual11_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,8]
def points : Finset C13.Point := {3,6,7,8}
def columns : List Code := [379,439,631,699,829,830,919,935,967,979,995,1371,1374,1402,1431,1447,1461,1591,1623,1639,1654,1691,1693,1721,1822,1852,1882,1927,1957,1987,2411,2413,2425,2455,2471,2486,2615,2647,2663,2677,2731,2734,2746,2861,2876,2921,2951,2966,3011,3127,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3607,3623,3635,3637,3638,3655,3669,3670,3685,3686,3700,3723,3725,3726,3737,3738,3740,3753,3754,3756,3768,3788]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 135,1,2⟩,⟨.covers 139,1,6⟩,⟨.covers 77,1,9⟩,⟨.covers 149,1,4⟩,⟨.covers 2069,1,2⟩,⟨.covers 101,1,3⟩,⟨.covers 169,1,1⟩,⟨.covers 201,1,6⟩,⟨.covers 777,1,6⟩,⟨.covers 1289,1,12⟩,⟨.covers 209,1,17⟩,⟨.covers 1169,1,2⟩,⟨.covers 2577,1,2⟩,⟨.covers 225,1,14⟩,⟨.covers 1185,1,2⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,2⟩,⟨.covers 86,1,3⟩,⟨.covers 166,1,4⟩,⟨.covers 1062,1,2⟩,⟨.covers 198,1,11⟩,⟨.covers 154,1,1⟩,⟨.covers 106,1,12⟩,⟨.covers 778,1,6⟩,⟨.covers 2194,1,2⟩,⟨.covers 2210,1,2⟩,⟨.covers 1570,1,2⟩,⟨.covers 92,1,8⟩,⟨.covers 156,1,2⟩,⟨.covers 3332,1,6⟩,⟨.covers 184,1,1⟩,⟨.covers 216,1,4⟩,⟨.covers 232,1,15⟩,⟨.covers 3592,1,2⟩,⟨.covers 2384,1,12⟩,⟨.covers 1616,1,3⟩,⟨.covers 1424,1,2⟩,⟨.covers 2704,1,2⟩,⟨.covers 2832,1,6⟩,⟨.covers 864,1,3⟩,⟨.covers 2656,1,3⟩,⟨.covers 2464,1,2⟩,⟨.covers 1696,1,2⟩,⟨.covers 1824,1,6⟩,⟨.covers 1472,1,17⟩,⟨.covers 2496,1,17⟩,⟨.covers 3648,1,3⟩,⟨.incident 6,8,-6⟩,⟨.incident 7,8,-5⟩,⟨.incident 8,8,-2⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source11.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source11.rootCodes link11 points rows bound = true := by decide +kernel

end C13.Global.FastDual11_000
namespace C13.Global.FastDual11_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,11]
def points : Finset C13.Point := {3,6,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,855,871,883,919,935,947,967,979,995,1335,1371,1374,1402,1431,1447,1461,1591,1623,1639,1654,1691,1693,1721,1815,1819,1821,1822,1831,1843,1845,1846,1849,1850,1852,1863,1875,1878,1882,1891,1894,1906,1927,1939,1941,1945,1955,1957,1969,1987,2359,2411,2413,2425,2455,2486,2615,2647,2677,2731,2734,2746,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3277,3278,3292,3308,3351,3379,3405,3433,3478,3532,3607,3635,3669,3726,3754,3788]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 2055,1,5⟩,⟨.covers 1035,1,11⟩,⟨.covers 269,1,3⟩,⟨.covers 525,1,8⟩,⟨.covers 149,1,3⟩,⟨.covers 101,1,5⟩,⟨.covers 197,1,8⟩,⟨.covers 2309,1,3⟩,⟨.covers 201,1,3⟩,⟨.covers 2569,1,11⟩,⟨.covers 209,1,11⟩,⟨.covers 225,1,11⟩,⟨.covers 270,1,8⟩,⟨.covers 526,1,3⟩,⟨.covers 86,1,3⟩,⟨.covers 166,1,8⟩,⟨.covers 106,1,11⟩,⟨.covers 202,1,11⟩,⟨.covers 1316,1,3⟩,⟨.covers 1572,1,3⟩,⟨.covers 2820,1,3⟩,⟨.covers 184,1,11⟩,⟨.covers 216,1,11⟩,⟨.covers 232,1,3⟩,⟨.covers 2160,1,5⟩,⟨.covers 2384,1,5⟩,⟨.covers 1616,1,5⟩,⟨.covers 1424,1,5⟩,⟨.covers 3344,1,3⟩,⟨.covers 3600,1,5⟩,⟨.covers 3168,1,3⟩,⟨.covers 2464,1,3⟩,⟨.covers 3232,1,5⟩,⟨.covers 1824,1,3⟩,⟨.covers 3360,1,8⟩,⟨.covers 3616,1,5⟩,⟨.covers 1472,1,5⟩,⟨.covers 2496,1,5⟩,⟨.covers 2752,1,11⟩,⟨.covers 1856,1,3⟩,⟨.covers 1920,1,3⟩,⟨.covers 2944,1,8⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source11.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source11.rootCodes link11 points rows bound = true := by decide +kernel

end C13.Global.FastDual11_001
namespace C13.Global.FastDual11_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,8,9]
def points : Finset C13.Point := {3,6,8,9}
def columns : List Code := [379,439,631,699,701,702,727,743,829,830,956,967,979,995,1207,1246,1371,1374,1402,1431,1447,1461,1462,1498,1623,1639,1654,1691,1693,1721,1722,1724,1735,1766,1852,1987,2231,2285,2411,2413,2425,2455,2471,2485,2486,2537,2647,2663,2677,2731,2734,2745,2746,2748,2759,2773,2876,3011,3127,3223,3239,3251,3253,3254,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 263,1,4⟩,⟨.covers 139,1,4⟩,⟨.covers 1035,1,1⟩,⟨.covers 269,1,2⟩,⟨.covers 1037,1,5⟩,⟨.covers 1061,1,3⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,3⟩,⟨.covers 89,1,9⟩,⟨.covers 1049,1,2⟩,⟨.covers 777,1,13⟩,⟨.covers 2569,1,4⟩,⟨.covers 113,1,2⟩,⟨.covers 177,1,1⟩,⟨.covers 2577,1,1⟩,⟨.covers 270,1,6⟩,⟨.covers 2062,1,3⟩,⟨.covers 86,1,1⟩,⟨.covers 2070,1,1⟩,⟨.covers 166,1,1⟩,⟨.covers 774,1,9⟩,⟨.covers 1286,1,4⟩,⟨.covers 2566,1,4⟩,⟨.covers 154,1,2⟩,⟨.covers 2090,1,1⟩,⟨.covers 202,1,2⟩,⟨.covers 2314,1,10⟩,⟨.covers 2098,1,1⟩,⟨.covers 2194,1,2⟩,⟨.covers 2322,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 1122,1,1⟩,⟨.covers 3106,1,1⟩,⟨.covers 108,1,5⟩,⟨.covers 1796,1,15⟩,⟨.covers 2820,1,15⟩,⟨.covers 624,1,4⟩,⟨.covers 432,1,3⟩,⟨.covers 464,1,3⟩,⟨.covers 2256,1,5⟩,⟨.covers 1616,1,4⟩,⟨.covers 912,1,12⟩,⟨.covers 1424,1,4⟩,⟨.covers 2704,1,3⟩,⟨.covers 480,1,8⟩,⟨.covers 864,1,6⟩,⟨.covers 1376,1,10⟩,⟨.covers 2656,1,2⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,7⟩,⟨.covers 3360,1,1⟩,⟨.covers 1856,1,15⟩,⟨.covers 2880,1,15⟩,⟨.incident 8,8,-6⟩,⟨.incident 9,8,-4⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source11.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source11.rootCodes link11 points rows bound = true := by decide +kernel

end C13.Global.FastDual11_002
namespace C13.Global.FastDual11_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,8,11]
def points : Finset C13.Point := {3,6,8,11}
def columns : List Code := [379,439,631,695,699,701,702,727,743,829,830,919,935,949,950,956,967,979,995,1207,1246,1371,1374,1402,1431,1447,1461,1462,1498,1591,1623,1639,1654,1687,1691,1693,1694,1703,1715,1717,1718,1721,1722,1724,1735,1750,1766,1822,1852,1882,1927,1942,1957,1972,1987,2002,2231,2285,2411,2413,2425,2455,2486,2537,2615,2647,2677,2711,2731,2734,2739,2742,2746,2773,2921,2966,3127,3223,3251,3254,3277,3278,3292,3308,3433,3478,3607,3635,3669,3726,3734,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 773,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 209,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3332,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 624,1,1⟩,⟨.covers 1328,1,1⟩,⟨.covers 2384,1,1⟩,⟨.covers 3152,1,1⟩,⟨.covers 3616,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 1856,1,1⟩,⟨.covers 3648,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source11.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source11.rootCodes link11 points rows bound = true := by decide +kernel

end C13.Global.FastDual11_003
namespace C13.Global.FastDual11_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,9,11]
def points : Finset C13.Point := {3,6,9,11}
def columns : List Code := [379,439,631,699,701,702,727,743,829,830,855,871,953,954,956,967,979,995,1207,1246,1335,1371,1374,1402,1431,1447,1459,1461,1462,1498,1623,1639,1654,1691,1693,1721,1722,1724,1735,1766,1821,1852,1863,1894,1945,1976,1987,2018,2231,2285,2359,2411,2413,2425,2455,2483,2486,2537,2647,2677,2731,2734,2746,2773,2901,2986,3127,3223,3251,3254,3277,3278,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 71,1,5⟩,⟨.covers 263,1,1⟩,⟨.covers 2055,1,4⟩,⟨.covers 1035,1,10⟩,⟨.covers 147,1,1⟩,⟨.covers 1059,1,3⟩,⟨.covers 525,1,9⟩,⟨.covers 201,1,9⟩,⟨.covers 1161,1,3⟩,⟨.covers 777,1,3⟩,⟨.covers 2569,1,15⟩,⟨.covers 177,1,1⟩,⟨.covers 225,1,3⟩,⟨.covers 1185,1,1⟩,⟨.covers 897,1,3⟩,⟨.covers 1409,1,1⟩,⟨.covers 270,1,10⟩,⟨.covers 774,1,2⟩,⟨.covers 2566,1,3⟩,⟨.covers 3078,1,1⟩,⟨.covers 106,1,2⟩,⟨.covers 202,1,8⟩,⟨.covers 2314,1,10⟩,⟨.covers 226,1,2⟩,⟨.covers 156,1,2⟩,⟨.covers 300,1,1⟩,⟨.covers 2316,1,11⟩,⟨.covers 2572,1,12⟩,⟨.covers 404,1,2⟩,⟨.covers 420,1,1⟩,⟨.covers 804,1,1⟩,⟨.covers 1572,1,2⟩,⟨.covers 1796,1,2⟩,⟨.covers 2820,1,11⟩,⟨.covers 3332,1,1⟩,⟨.covers 3588,1,3⟩,⟨.covers 120,1,8⟩,⟨.covers 184,1,2⟩,⟨.covers 2824,1,5⟩,⟨.covers 3592,1,15⟩,⟨.covers 2224,1,1⟩,⟨.covers 2352,1,3⟩,⟨.covers 1584,1,7⟩,⟨.covers 464,1,2⟩,⟨.covers 3152,1,8⟩,⟨.covers 912,1,4⟩,⟨.covers 2704,1,11⟩,⟨.covers 3216,1,2⟩,⟨.covers 3344,1,2⟩,⟨.covers 864,1,1⟩,⟨.covers 2656,1,11⟩,⟨.covers 3168,1,12⟩,⟨.covers 1728,1,5⟩,⟨.covers 1856,1,1⟩,⟨.incident 3,8,-4⟩,⟨.incident 9,8,-4⟩,⟨.incident 11,8,-2⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source11.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source11.rootCodes link11 points rows bound = true := by decide +kernel

end C13.Global.FastDual11_004
namespace C13.Global.FastDual11_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,7,8,9]
def points : Finset C13.Point := {6,7,8,9}
def columns : List Code := [127,191,223,239,319,351,367,379,415,431,439,463,575,607,623,631,671,687,699,719,799,815,829,830,847,911,967,971,979,995,1087,1119,1135,1150,1183,1199,1213,1231,1311,1327,1341,1342,1359,1371,1374,1387,1402,1423,1431,1447,1453,1461,1567,1583,1597,1598,1615,1623,1639,1646,1654,1679,1691,1693,1707,1721,1807,1852,1987,2111,2143,2159,2173,2207,2223,2238,2255,2335,2351,2365,2366,2383,2395,2411,2413,2425,2447,2455,2462,2471,2486,2591,2607,2621,2622,2639,2647,2653,2663,2677,2703,2715,2731,2734,2746,2831,2876,3011,3103,3119,3127,3131,3133,3134,3151,3165,3166,3181,3182,3196,3215,3229,3230,3245,3246,3260,3277,3278,3292,3308,3343,3358,3373,3388,3403,3418,3433,3448,3463,3478,3493,3508,3599,3613,3630,3644,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 169,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 1161,1,1⟩,⟨.covers 2182,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 2186,1,1⟩,⟨.covers 464,1,3⟩,⟨.covers 2256,1,3⟩,⟨.covers 1424,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 1808,1,1⟩,⟨.covers 2832,1,1⟩,⟨.covers 480,1,3⟩,⟨.covers 2272,1,3⟩,⟨.covers 2464,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 1472,1,3⟩,⟨.covers 2496,1,3⟩,⟨.covers 3456,1,1⟩,⟨.covers 3712,1,1⟩,⟨.incident 7,8,-2⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source11.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source11.rootCodes link11 points rows bound = true := by decide +kernel

end C13.Global.FastDual11_005
