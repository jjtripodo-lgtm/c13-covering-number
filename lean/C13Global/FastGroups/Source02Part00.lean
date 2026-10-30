import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source02
namespace C13.Global.FastDual02_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,8]
def points : Finset C13.Point := {3,6,7,8}
def columns : List Code := [379,439,631,699,829,830,919,935,967,979,995,1371,1374,1402,1431,1447,1461,1591,1623,1639,1654,1691,1693,1721,1822,1852,1882,1927,1957,1987,2411,2413,2425,2455,2471,2486,2615,2647,2663,2677,2731,2734,2746,2861,2876,2921,2951,2966,3011,3127,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3607,3623,3635,3637,3638,3655,3669,3670,3685,3686,3700,3723,3725,3726,3737,3738,3740,3753,3754,3756,3768,3788]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 135,1,2⟩,⟨.covers 139,1,1⟩,⟨.covers 1035,1,2⟩,⟨.covers 2059,1,2⟩,⟨.covers 141,1,2⟩,⟨.covers 269,1,6⟩,⟨.covers 149,1,4⟩,⟨.covers 2069,1,2⟩,⟨.covers 101,1,3⟩,⟨.covers 89,1,2⟩,⟨.covers 169,1,3⟩,⟨.covers 201,1,12⟩,⟨.covers 1289,1,7⟩,⟨.covers 1169,1,2⟩,⟨.covers 2577,1,2⟩,⟨.covers 1313,1,2⟩,⟨.covers 78,1,3⟩,⟨.covers 270,1,6⟩,⟨.covers 86,1,3⟩,⟨.covers 166,1,4⟩,⟨.covers 1062,1,2⟩,⟨.covers 198,1,11⟩,⟨.covers 154,1,3⟩,⟨.covers 106,1,10⟩,⟨.covers 2322,1,2⟩,⟨.covers 2210,1,2⟩,⟨.covers 1570,1,2⟩,⟨.covers 108,1,3⟩,⟨.covers 172,1,2⟩,⟨.covers 212,1,15⟩,⟨.covers 228,1,9⟩,⟨.covers 184,1,1⟩,⟨.covers 3592,1,2⟩,⟨.covers 464,1,8⟩,⟨.covers 848,1,9⟩,⟨.covers 2384,1,10⟩,⟨.covers 1616,1,3⟩,⟨.covers 1424,1,2⟩,⟨.covers 2704,1,2⟩,⟨.covers 2832,1,6⟩,⟨.covers 480,1,8⟩,⟨.covers 864,1,9⟩,⟨.covers 1376,1,2⟩,⟨.covers 2656,1,3⟩,⟨.covers 2464,1,2⟩,⟨.covers 1696,1,2⟩,⟨.covers 1824,1,6⟩,⟨.covers 1472,1,17⟩,⟨.covers 2496,1,8⟩,⟨.covers 2752,1,9⟩,⟨.covers 3648,1,3⟩,⟨.covers 3456,1,6⟩,⟨.incident 6,8,-6⟩,⟨.incident 7,8,-5⟩,⟨.incident 8,8,-2⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source02.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source02.rootCodes link02 points rows bound = true := by decide +kernel

end C13.Global.FastDual02_000
namespace C13.Global.FastDual02_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,10]
def points : Finset C13.Point := {3,6,7,10}
def columns : List Code := [379,439,631,699,823,827,829,830,855,871,883,919,935,947,967,979,995,1335,1371,1374,1402,1447,1461,1591,1639,1654,1691,1693,1721,1819,1831,1843,1882,1894,1906,1945,1957,1969,2359,2411,2413,2425,2455,2471,2486,2615,2647,2663,2677,2731,2734,2746,2839,2855,2859,2861,2862,2867,2869,2870,2873,2874,2876,2887,2899,2901,2915,2917,2921,2929,2951,2963,2966,2979,2982,2986,2994,3011,3127,3277,3278,3292,3308,3367,3379,3406,3418,3493,3532,3623,3635,3686,3725,3737,3788]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 1031,1,1⟩,⟨.covers 2059,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 464,1,1⟩,⟨.covers 3344,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 480,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 2880,1,1⟩,⟨.covers 1920,1,1⟩,⟨.covers 2944,1,1⟩,⟨.covers 3456,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source02.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source02.rootCodes link02 points rows bound = true := by decide +kernel

end C13.Global.FastDual02_001
namespace C13.Global.FastDual02_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,8,9]
def points : Finset C13.Point := {3,6,8,9}
def columns : List Code := [379,439,631,699,701,702,727,743,829,830,956,967,979,995,1207,1246,1371,1374,1402,1431,1447,1461,1462,1498,1623,1639,1654,1691,1693,1721,1722,1724,1735,1766,1852,1987,2231,2285,2411,2413,2425,2455,2471,2485,2486,2537,2647,2663,2677,2731,2734,2745,2746,2748,2759,2773,2876,3011,3127,3223,3239,3251,3253,3254,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 71,1,4⟩,⟨.covers 135,1,1⟩,⟨.covers 263,1,1⟩,⟨.covers 139,1,7⟩,⟨.covers 2067,1,3⟩,⟨.covers 269,1,3⟩,⟨.covers 1037,1,9⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,6⟩,⟨.covers 1061,1,1⟩,⟨.covers 89,1,9⟩,⟨.covers 169,1,1⟩,⟨.covers 777,1,9⟩,⟨.covers 2569,1,3⟩,⟨.covers 1073,1,2⟩,⟨.covers 1553,1,3⟩,⟨.covers 2577,1,2⟩,⟨.covers 78,1,2⟩,⟨.covers 2062,1,6⟩,⟨.covers 86,1,1⟩,⟨.covers 1286,1,3⟩,⟨.covers 2566,1,5⟩,⟨.covers 154,1,3⟩,⟨.covers 2090,1,2⟩,⟨.covers 778,1,12⟩,⟨.covers 2314,1,7⟩,⟨.covers 2194,1,1⟩,⟨.covers 1570,1,3⟩,⟨.covers 1794,1,14⟩,⟨.covers 2818,1,14⟩,⟨.covers 3330,1,2⟩,⟨.covers 3586,1,2⟩,⟨.covers 92,1,2⟩,⟨.covers 116,1,3⟩,⟨.covers 180,1,1⟩,⟨.covers 184,1,2⟩,⟨.covers 232,1,2⟩,⟨.covers 1800,1,12⟩,⟨.covers 2824,1,12⟩,⟨.covers 464,1,5⟩,⟨.covers 2256,1,7⟩,⟨.covers 848,1,10⟩,⟨.covers 1616,1,7⟩,⟨.covers 1424,1,1⟩,⟨.covers 2704,1,5⟩,⟨.covers 480,1,1⟩,⟨.covers 1248,1,7⟩,⟨.covers 864,1,4⟩,⟨.covers 1376,1,9⟩,⟨.covers 928,1,10⟩,⟨.covers 2464,1,5⟩,⟨.covers 1696,1,5⟩,⟨.covers 3616,1,1⟩,⟨.covers 3648,1,4⟩,⟨.incident 6,8,-2⟩,⟨.incident 9,8,-6⟩]
def bound : Int := 8

theorem column_mask : listMask columns = restrictMask universeMask Source02.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source02.rootCodes link02 points rows bound = true := by decide +kernel

end C13.Global.FastDual02_002
namespace C13.Global.FastDual02_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,8,10]
def points : Finset C13.Point := {3,6,8,10}
def columns : List Code := [379,439,631,695,699,701,702,727,743,829,830,919,935,949,950,956,967,979,995,1207,1246,1371,1374,1402,1447,1461,1498,1591,1639,1654,1691,1693,1703,1715,1717,1721,1766,1882,1957,2231,2285,2411,2413,2425,2455,2471,2485,2486,2537,2615,2647,2663,2677,2711,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2759,2773,2789,2861,2876,2921,2951,2966,2981,2996,3011,3041,3127,3239,3251,3253,3277,3278,3292,3308,3418,3493,3623,3635,3686,3725,3737,3749,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 263,1,1⟩,⟨.covers 1031,1,4⟩,⟨.covers 139,1,5⟩,⟨.covers 2059,1,4⟩,⟨.covers 2067,1,1⟩,⟨.covers 2307,1,5⟩,⟨.covers 77,1,10⟩,⟨.covers 1037,1,2⟩,⟨.covers 537,1,2⟩,⟨.covers 777,1,7⟩,⟨.covers 1289,1,12⟩,⟨.covers 526,1,3⟩,⟨.covers 2062,1,6⟩,⟨.covers 2070,1,1⟩,⟨.covers 198,1,2⟩,⟨.covers 1286,1,6⟩,⟨.covers 3078,1,3⟩,⟨.covers 778,1,6⟩,⟨.covers 1546,1,5⟩,⟨.covers 2098,1,2⟩,⟨.covers 2194,1,1⟩,⟨.covers 610,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 2818,1,3⟩,⟨.covers 3330,1,12⟩,⟨.covers 3586,1,4⟩,⟨.covers 156,1,3⟩,⟨.covers 540,1,1⟩,⟨.covers 1292,1,5⟩,⟨.covers 1548,1,4⟩,⟨.covers 116,1,2⟩,⟨.covers 184,1,3⟩,⟨.covers 2824,1,3⟩,⟨.covers 3592,1,6⟩,⟨.covers 1136,1,9⟩,⟨.covers 2160,1,8⟩,⟨.covers 432,1,3⟩,⟨.covers 1200,1,8⟩,⟨.covers 1328,1,1⟩,⟨.covers 2352,1,2⟩,⟨.covers 464,1,9⟩,⟨.covers 720,1,1⟩,⟨.covers 2256,1,9⟩,⟨.covers 2832,1,4⟩,⟨.covers 3600,1,4⟩,⟨.covers 480,1,9⟩,⟨.covers 1248,1,9⟩,⟨.covers 1376,1,2⟩,⟨.covers 3168,1,3⟩,⟨.covers 1824,1,12⟩,⟨.covers 3360,1,12⟩,⟨.covers 1472,1,3⟩,⟨.covers 2496,1,1⟩,⟨.incident 10,8,-2⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source02.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source02.rootCodes link02 points rows bound = true := by decide +kernel

end C13.Global.FastDual02_003
namespace C13.Global.FastDual02_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,8,11]
def points : Finset C13.Point := {3,6,8,11}
def columns : List Code := [379,439,631,695,699,701,702,727,743,829,830,919,935,949,950,956,967,979,995,1207,1246,1371,1374,1402,1431,1447,1461,1462,1498,1591,1623,1639,1654,1687,1691,1693,1694,1703,1715,1717,1718,1721,1722,1724,1735,1750,1766,1822,1852,1882,1927,1942,1957,1972,1987,2002,2231,2285,2411,2413,2425,2455,2486,2537,2615,2647,2677,2711,2731,2734,2739,2742,2746,2773,2921,2966,3127,3223,3251,3254,3277,3278,3292,3308,3433,3478,3607,3635,3669,3726,3734,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 263,1,1⟩,⟨.covers 1031,1,2⟩,⟨.covers 2055,1,7⟩,⟨.covers 139,1,4⟩,⟨.covers 1035,1,5⟩,⟨.covers 1283,1,4⟩,⟨.covers 2307,1,6⟩,⟨.covers 2563,1,3⟩,⟨.covers 269,1,6⟩,⟨.covers 525,1,2⟩,⟨.covers 1037,1,6⟩,⟨.covers 1061,1,1⟩,⟨.covers 197,1,7⟩,⟨.covers 1073,1,4⟩,⟨.covers 593,1,2⟩,⟨.covers 2577,1,1⟩,⟨.covers 897,1,1⟩,⟨.covers 1409,1,1⟩,⟨.covers 78,1,6⟩,⟨.covers 270,1,2⟩,⟨.covers 2062,1,7⟩,⟨.covers 106,1,6⟩,⟨.covers 554,1,2⟩,⟨.covers 778,1,4⟩,⟨.covers 2314,1,1⟩,⟨.covers 2818,1,13⟩,⟨.covers 3330,1,13⟩,⟨.covers 172,1,4⟩,⟨.covers 2316,1,7⟩,⟨.covers 116,1,7⟩,⟨.covers 184,1,2⟩,⟨.covers 216,1,2⟩,⟨.covers 1800,1,2⟩,⟨.covers 2824,1,13⟩,⟨.covers 3336,1,13⟩,⟨.covers 3592,1,6⟩,⟨.covers 1136,1,2⟩,⟨.covers 432,1,2⟩,⟨.covers 2224,1,7⟩,⟨.covers 1328,1,1⟩,⟨.covers 2608,1,2⟩,⟨.covers 464,1,6⟩,⟨.covers 2384,1,13⟩,⟨.covers 3152,1,10⟩,⟨.covers 480,1,6⟩,⟨.covers 736,1,2⟩,⟨.covers 1248,1,7⟩,⟨.covers 2464,1,4⟩,⟨.covers 3232,1,2⟩,⟨.covers 1824,1,6⟩,⟨.covers 3616,1,3⟩,⟨.covers 2496,1,3⟩,⟨.covers 2752,1,3⟩,⟨.covers 1856,1,2⟩,⟨.incident 11,8,-5⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source02.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source02.rootCodes link02 points rows bound = true := by decide +kernel

end C13.Global.FastDual02_004
namespace C13.Global.FastDual02_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,9,10]
def points : Finset C13.Point := {3,6,9,10}
def columns : List Code := [379,439,631,699,701,702,727,743,829,830,855,871,953,954,956,967,979,995,1207,1246,1335,1371,1374,1402,1447,1459,1461,1498,1639,1654,1691,1693,1721,1766,1894,1945,2231,2285,2359,2411,2413,2425,2455,2471,2483,2485,2486,2537,2647,2663,2677,2731,2734,2745,2746,2748,2759,2773,2862,2876,2887,2901,2986,3000,3011,3025,3127,3239,3251,3253,3277,3278,3292,3308,3367,3379,3406,3418,3493,3505,3532,3544,3686,3737]
def rows : List LinearRow := [⟨.covers 2059,1,1⟩,⟨.covers 1539,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 2608,1,1⟩,⟨.covers 848,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 3152,1,1⟩,⟨.covers 480,1,1⟩,⟨.covers 1696,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source02.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source02.rootCodes link02 points rows bound = true := by decide +kernel

end C13.Global.FastDual02_005
namespace C13.Global.FastDual02_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,9,11]
def points : Finset C13.Point := {3,6,9,11}
def columns : List Code := [379,439,631,699,701,702,727,743,829,830,855,871,953,954,956,967,979,995,1207,1246,1335,1371,1374,1402,1431,1447,1459,1461,1462,1498,1623,1639,1654,1691,1693,1721,1722,1724,1735,1766,1821,1852,1863,1894,1945,1976,1987,2018,2231,2285,2359,2411,2413,2425,2455,2483,2486,2537,2647,2677,2731,2734,2746,2773,2901,2986,3127,3223,3251,3254,3277,3278,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 2055,1,4⟩,⟨.covers 75,1,3⟩,⟨.covers 1035,1,5⟩,⟨.covers 1059,1,4⟩,⟨.covers 2307,1,4⟩,⟨.covers 1539,1,3⟩,⟨.covers 141,1,2⟩,⟨.covers 525,1,4⟩,⟨.covers 777,1,4⟩,⟨.covers 2569,1,13⟩,⟨.covers 3081,1,11⟩,⟨.covers 449,1,2⟩,⟨.covers 1409,1,1⟩,⟨.covers 1665,1,2⟩,⟨.covers 270,1,4⟩,⟨.covers 198,1,1⟩,⟨.covers 774,1,4⟩,⟨.covers 2566,1,7⟩,⟨.covers 3078,1,4⟩,⟨.covers 106,1,5⟩,⟨.covers 3082,1,7⟩,⟨.covers 2818,1,13⟩,⟨.covers 3586,1,6⟩,⟨.covers 92,1,4⟩,⟨.covers 156,1,1⟩,⟨.covers 108,1,11⟩,⟨.covers 2316,1,2⟩,⟨.covers 2572,1,6⟩,⟨.covers 404,1,4⟩,⟨.covers 1316,1,3⟩,⟨.covers 184,1,2⟩,⟨.covers 216,1,2⟩,⟨.covers 1136,1,3⟩,⟨.covers 2224,1,4⟩,⟨.covers 2352,1,4⟩,⟨.covers 1584,1,5⟩,⟨.covers 2608,1,7⟩,⟨.covers 464,1,6⟩,⟨.covers 2256,1,1⟩,⟨.covers 2384,1,8⟩,⟨.covers 912,1,2⟩,⟨.covers 3216,1,4⟩,⟨.covers 2832,1,5⟩,⟨.covers 3600,1,13⟩,⟨.covers 736,1,6⟩,⟨.covers 864,1,1⟩,⟨.covers 2656,1,6⟩,⟨.covers 3168,1,2⟩,⟨.covers 2496,1,11⟩,⟨.covers 1728,1,2⟩,⟨.covers 2752,1,12⟩,⟨.incident 9,8,-1⟩,⟨.incident 11,8,-4⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source02.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source02.rootCodes link02 points rows bound = true := by decide +kernel

end C13.Global.FastDual02_006
namespace C13.Global.FastDual02_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,10,11]
def points : Finset C13.Point := {3,6,10,11}
def columns : List Code := [379,439,631,695,699,701,702,727,743,823,827,829,830,855,871,883,919,935,947,949,950,953,954,956,967,979,995,1207,1246,1335,1371,1374,1402,1447,1459,1461,1498,1591,1639,1654,1691,1693,1703,1715,1717,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2231,2285,2359,2411,2413,2425,2455,2483,2486,2537,2615,2647,2677,2711,2731,2734,2739,2742,2746,2773,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3251,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 270,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 464,1,1⟩,⟨.covers 2384,1,1⟩,⟨.covers 3152,1,1⟩,⟨.covers 736,1,1⟩,⟨.covers 1376,1,1⟩,⟨.covers 3232,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source02.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source02.rootCodes link02 points rows bound = true := by decide +kernel

end C13.Global.FastDual02_007
