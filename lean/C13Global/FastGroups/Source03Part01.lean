import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source03
namespace C13.Global.FastDual03_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,8,10]
def points : Finset C13.Point := {2,6,8,10}
def columns : List Code := [379,439,445,446,475,491,631,699,829,830,859,875,949,950,956,971,979,995,1211,1262,1371,1402,1447,1453,1461,1498,1595,1639,1646,1654,1691,1715,1721,1766,1882,1957,2235,2269,2395,2411,2425,2455,2462,2485,2486,2492,2507,2537,2619,2647,2653,2677,2715,2731,2739,2745,2746,2773,2846,2876,2891,2921,2966,2996,3011,3041,3131,3227,3251,3257,3277,3278,3292,3308,3418,3493,3611,3635,3662,3686,3737,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 2055,1,5⟩,⟨.covers 75,1,2⟩,⟨.covers 1035,1,4⟩,⟨.covers 2083,1,4⟩,⟨.covers 1283,1,7⟩,⟨.covers 2307,1,3⟩,⟨.covers 1539,1,4⟩,⟨.covers 77,1,4⟩,⟨.covers 525,1,4⟩,⟨.covers 1037,1,1⟩,⟨.covers 197,1,2⟩,⟨.covers 1541,1,8⟩,⟨.covers 201,1,1⟩,⟨.covers 777,1,4⟩,⟨.covers 3081,1,4⟩,⟨.covers 142,1,2⟩,⟨.covers 270,1,4⟩,⟨.covers 86,1,3⟩,⟨.covers 774,1,4⟩,⟨.covers 1286,1,6⟩,⟨.covers 3078,1,11⟩,⟨.covers 706,1,2⟩,⟨.covers 2434,1,2⟩,⟨.covers 2690,1,1⟩,⟨.covers 1794,1,13⟩,⟨.covers 3330,1,6⟩,⟨.covers 156,1,1⟩,⟨.covers 108,1,11⟩,⟨.covers 1292,1,12⟩,⟨.covers 1548,1,2⟩,⟨.covers 116,1,5⟩,⟨.covers 180,1,2⟩,⟨.covers 1796,1,5⟩,⟨.covers 3332,1,13⟩,⟨.covers 664,1,4⟩,⟨.covers 2600,1,3⟩,⟨.covers 2160,1,3⟩,⟨.covers 1200,1,4⟩,⟨.covers 2352,1,5⟩,⟨.covers 1584,1,4⟩,⟨.covers 720,1,6⟩,⟨.covers 3152,1,7⟩,⟨.covers 912,1,2⟩,⟨.covers 3216,1,4⟩,⟨.covers 480,1,6⟩,⟨.covers 864,1,1⟩,⟨.covers 1376,1,13⟩,⟨.covers 3168,1,2⟩,⟨.covers 1472,1,13⟩,⟨.covers 2496,1,2⟩,⟨.covers 1728,1,11⟩,⟨.incident 8,8,-1⟩,⟨.incident 10,8,-4⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source03.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source03.rootCodes link03 points rows bound = true := by decide +kernel

end C13.Global.FastDual03_008
namespace C13.Global.FastDual03_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,8,11]
def points : Finset C13.Point := {2,6,8,11}
def columns : List Code := [379,439,445,446,475,491,631,699,829,830,859,875,949,950,956,971,979,995,1211,1262,1371,1387,1402,1447,1453,1461,1462,1468,1483,1498,1595,1639,1646,1654,1691,1707,1715,1721,1722,1766,1837,1852,1867,1882,1957,1972,1987,2002,2235,2269,2411,2425,2455,2462,2486,2537,2619,2647,2653,2677,2731,2739,2746,2773,2921,2966,3131,3243,3251,3258,3277,3278,3292,3308,3433,3478,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 1031,1,5⟩,⟨.covers 75,1,2⟩,⟨.covers 2059,1,4⟩,⟨.covers 1043,1,4⟩,⟨.covers 1283,1,3⟩,⟨.covers 2563,1,4⟩,⟨.covers 269,1,6⟩,⟨.covers 773,1,3⟩,⟨.covers 2309,1,13⟩,⟨.covers 3077,1,12⟩,⟨.covers 897,1,2⟩,⟨.covers 1409,1,2⟩,⟨.covers 1665,1,1⟩,⟨.covers 78,1,4⟩,⟨.covers 526,1,4⟩,⟨.covers 86,1,5⟩,⟨.covers 198,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 778,1,4⟩,⟨.covers 3082,1,4⟩,⟨.covers 2818,1,13⟩,⟨.covers 3330,1,13⟩,⟨.covers 92,1,12⟩,⟨.covers 172,1,1⟩,⟨.covers 2316,1,13⟩,⟨.covers 180,1,2⟩,⟨.covers 228,1,1⟩,⟨.covers 1560,1,3⟩,⟨.covers 680,1,4⟩,⟨.covers 2824,1,5⟩,⟨.covers 3336,1,13⟩,⟨.covers 1136,1,3⟩,⟨.covers 2224,1,4⟩,⟨.covers 1328,1,5⟩,⟨.covers 2608,1,4⟩,⟨.covers 464,1,6⟩,⟨.covers 848,1,1⟩,⟨.covers 2384,1,13⟩,⟨.covers 736,1,6⟩,⟨.covers 2272,1,6⟩,⟨.covers 2656,1,8⟩,⟨.covers 928,1,2⟩,⟨.covers 2464,1,7⟩,⟨.covers 3232,1,4⟩,⟨.covers 1472,1,2⟩,⟨.covers 2752,1,12⟩,⟨.incident 8,8,-1⟩,⟨.incident 11,8,-4⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source03.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source03.rootCodes link03 points rows bound = true := by decide +kernel

end C13.Global.FastDual03_009
namespace C13.Global.FastDual03_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,9,10]
def points : Finset C13.Point := {2,6,9,10}
def columns : List Code := [379,439,443,445,446,475,491,631,699,829,830,923,939,953,954,956,971,979,995,1211,1262,1339,1371,1402,1435,1447,1453,1459,1461,1465,1498,1639,1646,1654,1691,1721,1766,1894,1945,2235,2269,2363,2395,2411,2425,2455,2459,2461,2462,2475,2483,2485,2486,2489,2490,2492,2507,2521,2537,2647,2653,2677,2715,2731,2745,2746,2773,2845,2876,2901,2955,2969,2986,3000,3011,3025,3131,3227,3251,3257,3277,3278,3292,3308,3355,3379,3418,3469,3481,3493,3505,3532,3544,3686,3737]
def rows : List LinearRow := [⟨.covers 135,1,3⟩,⟨.covers 1031,1,7⟩,⟨.covers 2055,1,6⟩,⟨.covers 75,1,4⟩,⟨.covers 523,1,3⟩,⟨.covers 1035,1,6⟩,⟨.covers 2083,1,1⟩,⟨.covers 2563,1,3⟩,⟨.covers 525,1,3⟩,⟨.covers 1037,1,7⟩,⟨.covers 293,1,1⟩,⟨.covers 197,1,4⟩,⟨.covers 773,1,5⟩,⟨.covers 1541,1,4⟩,⟨.covers 270,1,1⟩,⟨.covers 526,1,9⟩,⟨.covers 2062,1,9⟩,⟨.covers 2090,1,1⟩,⟨.covers 202,1,2⟩,⟨.covers 1546,1,2⟩,⟨.covers 3082,1,1⟩,⟨.covers 2098,1,2⟩,⟨.covers 338,1,2⟩,⟨.covers 2210,1,1⟩,⟨.covers 450,1,1⟩,⟨.covers 1794,1,12⟩,⟨.covers 2818,1,3⟩,⟨.covers 3330,1,4⟩,⟨.covers 3586,1,12⟩,⟨.covers 92,1,5⟩,⟨.covers 172,1,3⟩,⟨.covers 1548,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 180,1,5⟩,⟨.covers 3332,1,4⟩,⟨.covers 120,1,4⟩,⟨.covers 1800,1,12⟩,⟨.covers 3592,1,12⟩,⟨.covers 2160,1,6⟩,⟨.covers 688,1,1⟩,⟨.covers 1200,1,6⟩,⟨.covers 1584,1,5⟩,⟨.covers 2608,1,4⟩,⟨.covers 720,1,3⟩,⟨.covers 848,1,4⟩,⟨.covers 1616,1,7⟩,⟨.covers 3152,1,4⟩,⟨.covers 480,1,3⟩,⟨.covers 736,1,6⟩,⟨.covers 2272,1,6⟩,⟨.covers 3232,1,2⟩,⟨.covers 2848,1,4⟩,⟨.covers 3360,1,4⟩,⟨.covers 1472,1,7⟩,⟨.covers 1728,1,6⟩,⟨.covers 2752,1,3⟩,⟨.incident 10,8,-2⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source03.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source03.rootCodes link03 points rows bound = true := by decide +kernel

end C13.Global.FastDual03_010
namespace C13.Global.FastDual03_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,9,11]
def points : Finset C13.Point := {2,6,9,11}
def columns : List Code := [379,439,443,445,446,475,491,631,699,829,830,923,939,953,954,956,971,979,995,1211,1262,1339,1371,1387,1402,1435,1447,1451,1453,1454,1459,1461,1462,1465,1466,1468,1483,1498,1514,1639,1646,1654,1691,1707,1721,1722,1766,1838,1852,1894,1931,1945,1962,1976,1987,2018,2235,2269,2363,2411,2425,2455,2462,2475,2483,2486,2490,2537,2647,2653,2677,2731,2746,2773,2901,2986,3131,3243,3251,3258,3277,3278,3292,3308,3371,3379,3433,3470,3478,3498,3506,3532,3560,3669,3754]
def rows : List LinearRow := [⟨.covers 135,1,6⟩,⟨.covers 1031,1,4⟩,⟨.covers 75,1,2⟩,⟨.covers 2059,1,3⟩,⟨.covers 1043,1,2⟩,⟨.covers 2307,1,4⟩,⟨.covers 1539,1,6⟩,⟨.covers 269,1,4⟩,⟨.covers 1037,1,6⟩,⟨.covers 1049,1,1⟩,⟨.covers 201,1,2⟩,⟨.covers 777,1,4⟩,⟨.covers 2569,1,9⟩,⟨.covers 3081,1,4⟩,⟨.covers 1073,1,1⟩,⟨.covers 1169,1,1⟩,⟨.covers 353,1,2⟩,⟨.covers 449,1,1⟩,⟨.covers 526,1,7⟩,⟨.covers 278,1,2⟩,⟨.covers 198,1,7⟩,⟨.covers 2566,1,12⟩,⟨.covers 3078,1,6⟩,⟨.covers 2818,1,12⟩,⟨.covers 3586,1,12⟩,⟨.covers 156,1,2⟩,⟨.covers 284,1,1⟩,⟨.covers 2316,1,7⟩,⟨.covers 1548,1,3⟩,⟨.covers 2572,1,3⟩,⟨.covers 180,1,2⟩,⟨.covers 228,1,3⟩,⟨.covers 2820,1,11⟩,⟨.covers 3588,1,12⟩,⟨.covers 120,1,6⟩,⟨.covers 1136,1,4⟩,⟨.covers 688,1,1⟩,⟨.covers 2224,1,3⟩,⟨.covers 2352,1,4⟩,⟨.covers 1584,1,6⟩,⟨.covers 2608,1,8⟩,⟨.covers 464,1,4⟩,⟨.covers 1232,1,6⟩,⟨.covers 848,1,1⟩,⟨.covers 912,1,3⟩,⟨.covers 3216,1,4⟩,⟨.covers 2272,1,1⟩,⟨.covers 864,1,7⟩,⟨.covers 2656,1,4⟩,⟨.covers 3168,1,6⟩,⟨.covers 2496,1,6⟩,⟨.covers 2752,1,12⟩,⟨.covers 1856,1,3⟩,⟨.incident 11,8,-2⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source03.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source03.rootCodes link03 points rows bound = true := by decide +kernel

end C13.Global.FastDual03_011
namespace C13.Global.FastDual03_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,6,10,11]
def points : Finset C13.Point := {2,6,10,11}
def columns : List Code := [379,439,443,445,446,475,491,631,699,823,827,829,830,859,875,883,923,939,947,949,950,953,954,956,971,979,995,1211,1262,1339,1371,1402,1435,1447,1453,1459,1461,1465,1498,1595,1639,1646,1654,1691,1715,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2235,2269,2363,2411,2425,2455,2462,2475,2483,2486,2490,2537,2619,2647,2653,2677,2731,2739,2746,2773,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3251,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 1289,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 526,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 1232,1,1⟩,⟨.covers 736,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 2496,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source03.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source03.rootCodes link03 points rows bound = true := by decide +kernel

end C13.Global.FastDual03_012
namespace C13.Global.FastDual03_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,8,9]
def points : Finset C13.Point := {2,7,8,9}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,892,971,979,995,1147,1261,1371,1387,1401,1402,1447,1453,1461,1509,1639,1646,1653,1654,1660,1691,1707,1721,1739,1753,1852,1987,2171,2270,2395,2411,2425,2426,2455,2462,2486,2518,2647,2653,2677,2678,2684,2715,2731,2746,2763,2794,2876,3011,3131,3163,3179,3187,3193,3194,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 1541,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 1038,1,1⟩,⟨.covers 86,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 1286,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 1232,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 912,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 2272,1,1⟩,⟨.covers 864,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 2464,1,1⟩,⟨.incident 9,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source03.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source03.rootCodes link03 points rows bound = true := by decide +kernel

end C13.Global.FastDual03_013
namespace C13.Global.FastDual03_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,8,10]
def points : Finset C13.Point := {2,7,8,10}
def columns : List Code := [379,439,631,635,637,638,699,731,747,829,830,859,875,889,890,892,971,979,995,1147,1261,1371,1402,1447,1453,1461,1509,1595,1627,1639,1646,1651,1654,1658,1691,1721,1753,1882,1957,2171,2270,2395,2411,2425,2426,2455,2462,2486,2518,2619,2647,2651,2653,2654,2667,2675,2677,2678,2681,2682,2684,2715,2731,2746,2763,2778,2794,2846,2876,2891,2906,2921,2936,2966,3011,3026,3131,3163,3187,3194,3277,3278,3292,3308,3418,3493,3611,3635,3662,3674,3686,3698,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 2055,1,5⟩,⟨.covers 139,1,3⟩,⟨.covers 1035,1,3⟩,⟨.covers 2083,1,3⟩,⟨.covers 1283,1,8⟩,⟨.covers 2307,1,6⟩,⟨.covers 1539,1,3⟩,⟨.covers 525,1,6⟩,⟨.covers 2061,1,6⟩,⟨.covers 777,1,6⟩,⟨.covers 3081,1,5⟩,⟨.covers 657,1,2⟩,⟨.covers 2145,1,2⟩,⟨.covers 705,1,2⟩,⟨.covers 142,1,6⟩,⟨.covers 270,1,6⟩,⟨.covers 550,1,2⟩,⟨.covers 198,1,1⟩,⟨.covers 1286,1,3⟩,⟨.covers 3078,1,4⟩,⟨.covers 1794,1,11⟩,⟨.covers 3330,1,11⟩,⟨.covers 108,1,2⟩,⟨.covers 172,1,3⟩,⟨.covers 1292,1,8⟩,⟨.covers 1548,1,7⟩,⟨.covers 116,1,3⟩,⟨.covers 212,1,4⟩,⟨.covers 1796,1,8⟩,⟨.covers 2820,1,6⟩,⟨.covers 3332,1,11⟩,⟨.covers 184,1,6⟩,⟨.covers 368,1,3⟩,⟨.covers 1136,1,6⟩,⟨.covers 2224,1,5⟩,⟨.covers 2352,1,6⟩,⟨.covers 464,1,2⟩,⟨.covers 1232,1,7⟩,⟨.covers 912,1,6⟩,⟨.covers 1424,1,11⟩,⟨.covers 736,1,6⟩,⟨.covers 2272,1,6⟩,⟨.covers 864,1,3⟩,⟨.covers 1696,1,3⟩,⟨.covers 3616,1,5⟩,⟨.covers 1472,1,11⟩,⟨.covers 2496,1,4⟩,⟨.covers 3712,1,4⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source03.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source03.rootCodes link03 points rows bound = true := by decide +kernel

end C13.Global.FastDual03_014
namespace C13.Global.FastDual03_015
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,9,10]
def points : Finset C13.Point := {2,7,9,10}
def columns : List Code := [379,439,631,637,638,699,731,747,829,830,885,886,892,923,939,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1639,1646,1654,1691,1721,1753,1894,1945,2171,2270,2363,2395,2411,2419,2425,2426,2455,2462,2486,2518,2647,2653,2677,2678,2684,2715,2731,2746,2763,2794,2845,2876,2901,2932,2955,2986,3011,3042,3131,3163,3187,3194,3277,3278,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3686,3737]
def rows : List LinearRow := [⟨.covers 2055,1,5⟩,⟨.covers 139,1,2⟩,⟨.covers 1035,1,4⟩,⟨.covers 2083,1,4⟩,⟨.covers 1283,1,4⟩,⟨.covers 2563,1,3⟩,⟨.covers 77,1,2⟩,⟨.covers 525,1,4⟩,⟨.covers 149,1,3⟩,⟨.covers 197,1,11⟩,⟨.covers 773,1,4⟩,⟨.covers 1541,1,13⟩,⟨.covers 449,1,2⟩,⟨.covers 2369,1,1⟩,⟨.covers 2625,1,2⟩,⟨.covers 270,1,4⟩,⟨.covers 1286,1,8⟩,⟨.covers 3078,1,7⟩,⟨.covers 202,1,1⟩,⟨.covers 778,1,4⟩,⟨.covers 3082,1,4⟩,⟨.covers 1794,1,5⟩,⟨.covers 3586,1,6⟩,⟨.covers 92,1,1⟩,⟨.covers 156,1,4⟩,⟨.covers 1292,1,12⟩,⟨.covers 1548,1,13⟩,⟨.covers 116,1,2⟩,⟨.covers 180,1,5⟩,⟨.covers 212,1,2⟩,⟨.covers 344,1,4⟩,⟨.covers 2344,1,3⟩,⟨.covers 1800,1,13⟩,⟨.covers 3592,1,13⟩,⟨.covers 1136,1,4⟩,⟨.covers 2224,1,3⟩,⟨.covers 1328,1,4⟩,⟨.covers 2608,1,5⟩,⟨.covers 464,1,6⟩,⟨.covers 848,1,2⟩,⟨.covers 1616,1,7⟩,⟨.covers 3152,1,4⟩,⟨.covers 736,1,6⟩,⟨.covers 928,1,1⟩,⟨.covers 1696,1,13⟩,⟨.covers 3232,1,12⟩,⟨.covers 1728,1,6⟩,⟨.covers 2752,1,2⟩,⟨.incident 9,8,-1⟩,⟨.incident 10,8,-4⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source03.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source03.rootCodes link03 points rows bound = true := by decide +kernel

end C13.Global.FastDual03_015
