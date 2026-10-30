import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source13
namespace C13.Global.FastDual13_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,7]
def points : Finset C13.Point := {2,3,6,7}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,979,995,1371,1402,1447,1461,1639,1654,1691,1721,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1955,1957,1969,1987,2411,2425,2455,2486,2647,2677,2731,2746,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2915,2921,2929,2963,2966,2979,2986,2994,3011,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3477,3478,3493,3494,3508,3532,3635,3655,3669,3670,3685,3686,3700,3723,3737,3738,3753,3754,3768,3788,3847,3851,3853,3854,3859,3861,3862,3865,3866,3868,3875,3877,3878,3881,3882,3884,3889,3890,3892,3896,3907,3909,3910,3913,3914,3916,3921,3922,3924,3928,3937,3938,3940,3944,3952,3971,3973,3974,3977,3978,3980,3985,3986,3988,3992,4001,4002,4004,4008,4016,4033,4034,4036,4040,4048,4064]
def rows : List LinearRow := [⟨.covers 71,1,8⟩,⟨.covers 135,1,5⟩,⟨.covers 75,1,5⟩,⟨.covers 139,1,7⟩,⟨.covers 77,1,34⟩,⟨.covers 149,1,7⟩,⟨.covers 101,1,5⟩,⟨.covers 89,1,3⟩,⟨.covers 169,1,4⟩,⟨.covers 209,1,34⟩,⟨.covers 225,1,34⟩,⟨.covers 1185,1,1⟩,⟨.covers 2369,1,2⟩,⟨.covers 2625,1,5⟩,⟨.covers 1409,1,2⟩,⟨.covers 1665,1,1⟩,⟨.covers 78,1,34⟩,⟨.covers 86,1,5⟩,⟨.covers 166,1,3⟩,⟨.covers 154,1,5⟩,⟨.covers 106,1,8⟩,⟨.covers 1106,1,1⟩,⟨.covers 1346,1,2⟩,⟨.covers 1602,1,1⟩,⟨.covers 2434,1,2⟩,⟨.covers 2690,1,5⟩,⟨.covers 92,1,34⟩,⟨.covers 108,1,34⟩,⟨.covers 180,1,1⟩,⟨.covers 1604,1,3⟩,⟨.covers 1412,1,5⟩,⟨.covers 2436,1,2⟩,⟨.covers 120,1,1⟩,⟨.covers 1352,1,5⟩,⟨.covers 2376,1,2⟩,⟨.covers 1672,1,3⟩,⟨.covers 2160,1,6⟩,⟨.covers 2224,1,6⟩,⟨.covers 2384,1,3⟩,⟨.covers 1616,1,7⟩,⟨.covers 2704,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 2464,1,2⟩,⟨.covers 1696,1,7⟩,⟨.covers 1728,1,23⟩,⟨.incident 6,8,-17⟩,⟨.incident 7,8,-16⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source13.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source13.rootCodes link13 points rows bound = true := by decide +kernel

end C13.Global.FastDual13_000
namespace C13.Global.FastDual13_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,9]
def points : Finset C13.Point := {2,3,6,9}
def columns : List Code := [379,439,631,699,829,830,953,954,956,979,995,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1721,1722,1766,1852,1894,1945,1976,1987,2018,2411,2425,2455,2483,2485,2486,2537,2647,2677,2731,2745,2746,2773,2876,2901,2986,3000,3011,3025,3251,3277,3278,3292,3308,3379,3403,3417,3418,3433,3434,3448,3463,3475,3477,3478,3491,3493,3494,3505,3506,3508,3529,3530,3532,3544,3560,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 139,1,1⟩,⟨.covers 77,1,14⟩,⟨.covers 269,1,15⟩,⟨.covers 149,1,3⟩,⟨.covers 197,1,3⟩,⟨.covers 2309,1,3⟩,⟨.covers 1541,1,12⟩,⟨.covers 89,1,2⟩,⟨.covers 1049,1,2⟩,⟨.covers 169,1,2⟩,⟨.covers 1289,1,4⟩,⟨.covers 2569,1,3⟩,⟨.covers 225,1,6⟩,⟨.covers 2145,1,2⟩,⟨.covers 1185,1,2⟩,⟨.covers 1313,1,2⟩,⟨.covers 78,1,17⟩,⟨.covers 270,1,6⟩,⟨.covers 86,1,12⟩,⟨.covers 166,1,3⟩,⟨.covers 774,1,9⟩,⟨.covers 1286,1,3⟩,⟨.covers 154,1,2⟩,⟨.covers 1050,1,2⟩,⟨.covers 106,1,2⟩,⟨.covers 2090,1,2⟩,⟨.covers 2314,1,4⟩,⟨.covers 1546,1,1⟩,⟨.covers 210,1,6⟩,⟨.covers 2194,1,2⟩,⟨.covers 2322,1,2⟩,⟨.covers 92,1,8⟩,⟨.covers 156,1,9⟩,⟨.covers 108,1,17⟩,⟨.covers 2316,1,3⟩,⟨.covers 1548,1,15⟩,⟨.covers 180,1,3⟩,⟨.covers 2820,1,9⟩,⟨.covers 3332,1,3⟩,⟨.covers 120,1,6⟩,⟨.covers 184,1,2⟩,⟨.covers 2824,1,2⟩,⟨.covers 3336,1,2⟩,⟨.covers 3592,1,3⟩,⟨.covers 2656,1,10⟩,⟨.covers 3616,1,2⟩,⟨.covers 1728,1,3⟩,⟨.covers 2752,1,6⟩,⟨.covers 1920,1,2⟩,⟨.incident 2,8,-6⟩,⟨.incident 3,8,-5⟩,⟨.incident 6,8,-2⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source13.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source13.rootCodes link13 points rows bound = true := by decide +kernel

end C13.Global.FastDual13_001
namespace C13.Global.FastDual13_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,11]
def points : Finset C13.Point := {2,3,6,11}
def columns : List Code := [379,439,631,699,823,827,829,830,883,947,949,950,953,954,956,979,995,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1946,1955,1957,1958,1969,1970,1972,1976,1987,2002,2018,2411,2425,2455,2483,2486,2537,2647,2677,2731,2739,2746,2773,2839,2859,2867,2901,2921,2929,2966,2986,2994,3251,3277,3278,3292,3308,3379,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 2055,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 1289,1,1⟩,⟨.covers 209,1,1⟩,⟨.covers 225,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 166,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 3344,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 3616,1,1⟩,⟨.covers 1856,1,1⟩,⟨.covers 2880,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source13.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source13.rootCodes link13 points rows bound = true := by decide +kernel

end C13.Global.FastDual13_002
namespace C13.Global.FastDual13_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,9]
def points : Finset C13.Point := {2,6,7,9}
def columns : List Code := [379,439,631,699,829,830,923,939,971,979,995,1339,1371,1387,1402,1447,1453,1461,1639,1646,1654,1691,1707,1721,1838,1852,1894,1931,1945,1987,2363,2395,2411,2425,2455,2462,2486,2647,2653,2677,2715,2731,2746,2845,2876,2901,2955,2986,3011,3131,3277,3278,3292,3308,3355,3371,3379,3385,3386,3403,3417,3418,3433,3434,3448,3463,3469,3470,3477,3478,3484,3493,3494,3500,3508,3532,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,3⟩,⟨.covers 2055,1,2⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,3⟩,⟨.covers 1043,1,2⟩,⟨.covers 77,1,1⟩,⟨.covers 525,1,10⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,12⟩,⟨.covers 1541,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 169,1,5⟩,⟨.covers 2089,1,2⟩,⟨.covers 201,1,10⟩,⟨.covers 1289,1,1⟩,⟨.covers 209,1,16⟩,⟨.covers 1169,1,3⟩,⟨.covers 225,1,14⟩,⟨.covers 1185,1,3⟩,⟨.covers 78,1,9⟩,⟨.covers 86,1,1⟩,⟨.covers 166,1,3⟩,⟨.covers 774,1,10⟩,⟨.covers 2566,1,9⟩,⟨.covers 154,1,6⟩,⟨.covers 106,1,3⟩,⟨.covers 202,1,2⟩,⟨.covers 2194,1,3⟩,⟨.covers 1298,1,2⟩,⟨.covers 2594,1,3⟩,⟨.covers 180,1,1⟩,⟨.covers 212,1,11⟩,⟨.covers 228,1,11⟩,⟨.covers 3332,1,4⟩,⟨.covers 120,1,1⟩,⟨.covers 3592,1,8⟩,⟨.covers 2160,1,1⟩,⟨.covers 2384,1,1⟩,⟨.covers 1616,1,12⟩,⟨.covers 2704,1,3⟩,⟨.covers 1808,1,10⟩,⟨.covers 864,1,2⟩,⟨.covers 2464,1,1⟩,⟨.covers 1696,1,3⟩,⟨.covers 2848,1,10⟩,⟨.covers 2496,1,3⟩,⟨.covers 1728,1,16⟩,⟨.covers 2752,1,2⟩,⟨.covers 2880,1,11⟩,⟨.covers 3392,1,3⟩,⟨.incident 6,8,-2⟩,⟨.incident 7,8,-4⟩,⟨.incident 9,8,-5⟩]
def bound : Int := 6

theorem column_mask : listMask columns = restrictMask universeMask Source13.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source13.rootCodes link13 points rows bound = true := by decide +kernel

end C13.Global.FastDual13_003
namespace C13.Global.FastDual13_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,7,11]
def points : Finset C13.Point := {2,6,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,859,875,883,923,939,947,971,979,995,1339,1371,1387,1402,1447,1453,1461,1595,1639,1646,1654,1691,1707,1721,1819,1831,1835,1837,1838,1843,1845,1846,1849,1850,1852,1867,1875,1882,1891,1894,1898,1906,1931,1939,1945,1955,1957,1961,1969,1987,2363,2411,2425,2455,2462,2486,2619,2647,2653,2677,2731,2746,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3277,3278,3292,3308,3371,3379,3433,3470,3478,3532,3627,3635,3661,3669,3754,3788]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 209,1,1⟩,⟨.covers 225,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 86,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 3344,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 1856,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source13.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source13.rootCodes link13 points rows bound = true := by decide +kernel

end C13.Global.FastDual13_004
namespace C13.Global.FastDual13_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,9,11]
def points : Finset C13.Point := {2,6,9,11}
def columns : List Code := [379,439,443,445,446,475,491,631,699,829,830,923,939,953,954,956,971,979,995,1211,1262,1339,1371,1387,1402,1435,1447,1451,1453,1454,1459,1461,1462,1465,1466,1468,1483,1498,1514,1639,1646,1654,1691,1707,1721,1722,1766,1838,1852,1894,1931,1945,1962,1976,1987,2018,2235,2269,2363,2411,2425,2455,2462,2475,2483,2486,2490,2537,2647,2653,2677,2731,2746,2773,2901,2986,3131,3243,3251,3258,3277,3278,3292,3308,3371,3379,3433,3470,3478,3498,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 225,1,1⟩,⟨.covers 2062,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 1584,1,1⟩,⟨.covers 2608,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 3392,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source13.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source13.rootCodes link13 points rows bound = true := by decide +kernel

end C13.Global.FastDual13_005
namespace C13.Global.FastDual13_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,11]
def points : Finset C13.Point := {2,7,9,11}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1387,1395,1401,1402,1447,1453,1461,1509,1639,1646,1653,1654,1660,1691,1707,1721,1739,1753,1838,1852,1894,1908,1931,1945,1987,2001,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2647,2653,2677,2731,2746,2794,2901,2986,3131,3179,3187,3193,3277,3278,3292,3308,3371,3379,3433,3441,3470,3478,3532,3540,3669,3754]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 2566,1,2⟩,⟨.covers 2316,1,1⟩,⟨.covers 2572,1,2⟩,⟨.covers 228,1,1⟩,⟨.covers 2820,1,2⟩,⟨.covers 3588,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 2224,1,1⟩,⟨.covers 1584,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 864,1,1⟩,⟨.covers 2656,1,1⟩,⟨.incident 2,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source13.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source13.rootCodes link13 points rows bound = true := by decide +kernel

end C13.Global.FastDual13_006
