import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source53
namespace C13.Global.FastDual53_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,3,9]
def points : Finset C13.Point := {1,2,3,9}
def columns : List Code := [247,251,253,254,499,501,502,505,506,508,755,757,758,761,762,764,829,885,892,953,956,979,995,1009,1010,1012,1016,1267,1269,1270,1273,1274,1276,1371,1395,1401,1402,1461,1491,1497,1498,1509,1521,1522,1524,1528,1639,1653,1654,1721,1753,1763,1766,1777,1778,1780,1784,1852,1894,1908,1945,1976,1987,2001,2018,2032,2291,2293,2294,2297,2298,2300,2425,2455,2483,2485,2486,2515,2517,2518,2537,2545,2546,2548,2552,2677,2731,2745,2746,2773,2787,2794,2801,2802,2804,2808,2876,2901,2932,2986,3000,3011,3025,3042,3056,3187,3251,3277,3285,3289,3292,3301,3305,3308,3313,3314,3316,3320,3379,3411,3417,3418,3433,3441,3442,3448,3475,3477,3478,3493,3505,3506,3508,3525,3529,3532,3537,3538,3540,3544,3553,3556,3560,3568,3669,3686,3700,3737,3754,3768,3793,3810,3824,3854,3868,3910,3924,3978,3992,4034,4048]
def rows : List LinearRow := [⟨.covers 39,1,3⟩,⟨.covers 2055,1,4⟩,⟨.covers 43,1,3⟩,⟨.covers 1035,1,4⟩,⟨.covers 77,1,4⟩,⟨.covers 525,1,3⟩,⟨.covers 1553,1,1⟩,⟨.covers 2577,1,1⟩,⟨.covers 833,1,1⟩,⟨.covers 2625,1,1⟩,⟨.covers 897,1,1⟩,⟨.covers 1665,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 1074,1,2⟩,⟨.covers 2098,1,2⟩,⟨.covers 3090,1,2⟩,⟨.covers 3106,1,1⟩,⟨.covers 450,1,1⟩,⟨.covers 2132,1,1⟩,⟨.covers 420,1,2⟩,⟨.covers 1188,1,2⟩,⟨.covers 1316,1,1⟩,⟨.covers 1412,1,2⟩,⟨.covers 1176,1,1⟩,⟨.covers 360,1,2⟩,⟨.covers 2152,1,2⟩,⟨.covers 2344,1,1⟩,⟨.covers 2376,1,2⟩,⟨.covers 1584,1,1⟩,⟨.covers 2608,1,1⟩,⟨.covers 720,1,2⟩,⟨.covers 1808,1,1⟩,⟨.covers 2832,1,1⟩,⟨.covers 864,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 928,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 1856,1,1⟩,⟨.covers 3648,1,1⟩,⟨.covers 2944,1,1⟩,⟨.covers 3712,1,1⟩,⟨.incident 1,8,3⟩,⟨.incident 2,8,3⟩,⟨.incident 3,8,3⟩,⟨.incident 9,8,1⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_000
namespace C13.Global.FastDual53_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,6,9]
def points : Finset C13.Point := {1,2,6,9}
def columns : List Code := [445,475,829,953,956,971,979,995,1371,1402,1453,1461,1465,1468,1498,1639,1646,1654,1721,1766,1852,1894,1945,1976,1987,2018,2235,2269,2425,2455,2459,2461,2462,2483,2485,2486,2489,2490,2492,2521,2537,2653,2677,2731,2745,2746,2773,2845,2876,2901,2955,2969,2986,3000,3011,3025,3131,3251,3257,3258,3277,3292,3308,3355,3379,3385,3386,3417,3418,3433,3448,3469,3475,3477,3478,3481,3482,3484,3493,3497,3500,3505,3506,3508,3512,3529,3532,3544,3560,3669,3686,3700,3737,3754,3768,3854,3868,3910,3924,3978,3992,4034,4048]
def rows : List LinearRow := [⟨.covers 39,1,14⟩,⟨.covers 135,1,17⟩,⟨.covers 43,1,3⟩,⟨.covers 1035,1,4⟩,⟨.covers 1283,1,10⟩,⟨.covers 1539,1,3⟩,⟨.covers 2563,1,8⟩,⟨.covers 45,1,3⟩,⟨.covers 525,1,10⟩,⟨.covers 1037,1,4⟩,⟨.covers 773,1,1⟩,⟨.covers 3077,1,10⟩,⟨.covers 1073,1,1⟩,⟨.covers 1553,1,3⟩,⟨.covers 1185,1,1⟩,⟨.covers 705,1,1⟩,⟨.covers 2625,1,1⟩,⟨.covers 46,1,17⟩,⟨.covers 142,1,17⟩,⟨.covers 86,1,17⟩,⟨.covers 198,1,17⟩,⟨.covers 1286,1,1⟩,⟨.covers 58,1,3⟩,⟨.covers 202,1,10⟩,⟨.covers 778,1,3⟩,⟨.covers 178,1,8⟩,⟨.covers 210,1,4⟩,⟨.covers 3106,1,3⟩,⟨.covers 2818,1,3⟩,⟨.covers 3586,1,1⟩,⟨.covers 92,1,3⟩,⟨.covers 172,1,3⟩,⟨.covers 180,1,8⟩,⟨.covers 212,1,11⟩,⟨.covers 1316,1,3⟩,⟨.covers 1796,1,3⟩,⟨.covers 2820,1,3⟩,⟨.covers 120,1,11⟩,⟨.covers 1560,1,6⟩,⟨.covers 232,1,11⟩,⟨.covers 2600,1,3⟩,⟨.covers 1800,1,3⟩,⟨.covers 848,1,8⟩,⟨.covers 864,1,10⟩,⟨.covers 2656,1,12⟩,⟨.covers 928,1,3⟩,⟨.covers 3712,1,3⟩,⟨.incident 1,8,-3⟩,⟨.incident 2,8,-3⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_001
namespace C13.Global.FastDual53_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,6,10]
def points : Finset C13.Point := {1,2,6,10}
def columns : List Code := [445,475,829,949,953,956,971,979,995,1371,1402,1453,1461,1465,1498,1639,1646,1654,1721,1766,1882,1894,1906,1945,1957,1969,2235,2269,2425,2455,2459,2461,2462,2483,2485,2486,2489,2490,2492,2521,2537,2653,2677,2731,2739,2745,2746,2773,2845,2869,2873,2876,2901,2905,2921,2929,2955,2963,2965,2966,2969,2970,2972,2979,2985,2986,2993,2994,2996,3000,3011,3017,3025,3041,3131,3251,3257,3277,3292,3308,3355,3379,3418,3469,3481,3493,3505,3532,3544,3635,3686,3737,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 135,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3332,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3592,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 1232,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_002
namespace C13.Global.FastDual53_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,6,11]
def points : Finset C13.Point := {1,2,6,11}
def columns : List Code := [445,475,829,949,953,956,971,979,995,1371,1402,1453,1461,1465,1468,1498,1639,1646,1654,1721,1766,1837,1845,1849,1852,1867,1875,1882,1891,1894,1898,1906,1945,1957,1961,1964,1969,1972,1976,1987,1994,2002,2018,2235,2269,2425,2455,2462,2483,2486,2490,2537,2653,2677,2731,2739,2746,2773,2901,2921,2929,2966,2986,2994,3131,3251,3258,3277,3292,3308,3379,3433,3478,3506,3532,3560,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 39,1,17⟩,⟨.covers 135,1,18⟩,⟨.covers 83,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 163,1,4⟩,⟨.covers 1283,1,4⟩,⟨.covers 2563,1,1⟩,⟨.covers 53,1,5⟩,⟨.covers 197,1,11⟩,⟨.covers 1157,1,2⟩,⟨.covers 773,1,5⟩,⟨.covers 3077,1,1⟩,⟨.covers 3089,1,1⟩,⟨.covers 1185,1,1⟩,⟨.covers 705,1,1⟩,⟨.covers 1409,1,1⟩,⟨.covers 46,1,8⟩,⟨.covers 142,1,18⟩,⟨.covers 86,1,10⟩,⟨.covers 198,1,18⟩,⟨.covers 1286,1,13⟩,⟨.covers 2566,1,10⟩,⟨.covers 3078,1,5⟩,⟨.covers 58,1,2⟩,⟨.covers 1050,1,1⟩,⟨.covers 202,1,2⟩,⟨.covers 778,1,2⟩,⟨.covers 3082,1,1⟩,⟨.covers 3586,1,2⟩,⟨.covers 540,1,2⟩,⟨.covers 108,1,10⟩,⟨.covers 172,1,5⟩,⟨.covers 1292,1,5⟩,⟨.covers 2572,1,12⟩,⟨.covers 116,1,8⟩,⟨.covers 180,1,5⟩,⟨.covers 1796,1,5⟩,⟨.covers 2820,1,8⟩,⟨.covers 120,1,2⟩,⟨.covers 568,1,1⟩,⟨.covers 216,1,2⟩,⟨.covers 792,1,1⟩,⟨.covers 2696,1,1⟩,⟨.covers 2824,1,2⟩,⟨.covers 3592,1,1⟩,⟨.covers 2608,1,1⟩,⟨.covers 720,1,2⟩,⟨.covers 848,1,1⟩,⟨.covers 3152,1,12⟩,⟨.covers 2496,1,2⟩,⟨.incident 1,8,-4⟩,⟨.incident 2,8,-12⟩]
def bound : Int := 3

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_003
namespace C13.Global.FastDual53_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,7,9]
def points : Finset C13.Point := {1,2,7,9}
def columns : List Code := [637,747,829,885,892,971,979,995,1147,1261,1371,1395,1401,1402,1453,1461,1509,1639,1646,1653,1654,1660,1721,1753,1852,1894,1908,1945,1987,2001,2425,2455,2462,2486,2518,2653,2677,2684,2731,2746,2794,2845,2876,2901,2932,2955,2986,3011,3042,3131,3187,3193,3194,3277,3292,3308,3355,3379,3385,3386,3411,3417,3418,3433,3441,3442,3448,3469,3477,3478,3484,3493,3500,3508,3525,3532,3540,3556,3669,3686,3700,3737,3754,3768,3854,3868,3910,3924,3978,3992,4034,4048]
def rows : List LinearRow := [⟨.covers 39,1,25⟩,⟨.covers 135,1,25⟩,⟨.covers 1035,1,8⟩,⟨.covers 1283,1,8⟩,⟨.covers 2563,1,25⟩,⟨.covers 46,1,25⟩,⟨.covers 142,1,17⟩,⟨.covers 54,1,17⟩,⟨.covers 1286,1,17⟩,⟨.covers 2566,1,8⟩,⟨.covers 58,1,8⟩,⟨.covers 154,1,8⟩,⟨.covers 202,1,25⟩,⟨.covers 114,1,8⟩,⟨.covers 178,1,8⟩,⟨.covers 210,1,25⟩,⟨.covers 1298,1,8⟩,⟨.covers 3106,1,8⟩,⟨.covers 928,1,25⟩,⟨.incident 1,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_004
namespace C13.Global.FastDual53_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,7,10]
def points : Finset C13.Point := {1,2,7,10}
def columns : List Code := [637,747,829,885,889,892,971,979,995,1147,1261,1371,1395,1402,1453,1461,1509,1639,1646,1651,1654,1658,1721,1753,1882,1894,1906,1945,1957,1969,2425,2455,2462,2486,2518,2653,2677,2681,2684,2731,2746,2794,2845,2869,2873,2876,2901,2905,2908,2921,2929,2932,2936,2955,2963,2966,2970,2979,2986,2994,3011,3018,3026,3042,3131,3187,3194,3277,3292,3308,3355,3379,3418,3442,3469,3493,3532,3556,3635,3686,3698,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 135,1,2⟩,⟨.covers 83,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 1541,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 86,1,1⟩,⟨.covers 166,1,1⟩,⟨.covers 1286,1,2⟩,⟨.covers 3078,1,2⟩,⟨.covers 172,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 1472,1,1⟩,⟨.incident 1,8,-1⟩,⟨.incident 2,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_005
namespace C13.Global.FastDual53_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,7,11]
def points : Finset C13.Point := {1,2,7,11}
def columns : List Code := [637,747,829,885,889,892,971,979,995,1147,1261,1371,1395,1401,1402,1453,1461,1509,1639,1643,1645,1646,1651,1653,1654,1657,1658,1660,1721,1753,1769,1837,1845,1849,1852,1867,1875,1881,1882,1891,1893,1894,1897,1898,1900,1905,1906,1908,1912,1945,1957,1961,1969,1987,1993,2001,2017,2425,2455,2462,2486,2518,2653,2677,2681,2731,2746,2794,2901,2921,2929,2966,2986,2994,3131,3187,3193,3277,3292,3308,3379,3433,3441,3478,3532,3540,3627,3635,3661,3669,3689,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 39,1,11⟩,⟨.covers 135,1,6⟩,⟨.covers 83,1,6⟩,⟨.covers 163,1,6⟩,⟨.covers 1283,1,2⟩,⟨.covers 2307,1,6⟩,⟨.covers 2563,1,5⟩,⟨.covers 141,1,6⟩,⟨.covers 53,1,5⟩,⟨.covers 197,1,3⟩,⟨.covers 773,1,2⟩,⟨.covers 3077,1,3⟩,⟨.covers 1289,1,1⟩,⟨.covers 46,1,11⟩,⟨.covers 142,1,11⟩,⟨.covers 54,1,7⟩,⟨.covers 166,1,4⟩,⟨.covers 198,1,11⟩,⟨.covers 774,1,2⟩,⟨.covers 2566,1,9⟩,⟨.covers 3078,1,8⟩,⟨.covers 58,1,5⟩,⟨.covers 202,1,5⟩,⟨.covers 778,1,5⟩,⟨.covers 3082,1,6⟩,⟨.covers 1794,1,3⟩,⟨.covers 92,1,3⟩,⟨.covers 300,1,4⟩,⟨.covers 2572,1,9⟩,⟨.covers 116,1,4⟩,⟨.covers 180,1,1⟩,⟨.covers 228,1,3⟩,⟨.covers 1796,1,4⟩,⟨.covers 184,1,6⟩,⟨.covers 216,1,6⟩,⟨.covers 1304,1,3⟩,⟨.covers 2824,1,3⟩,⟨.covers 3336,1,8⟩,⟨.covers 2160,1,3⟩,⟨.covers 1200,1,5⟩,⟨.covers 1328,1,1⟩,⟨.covers 720,1,5⟩,⟨.covers 3152,1,3⟩,⟨.covers 3344,1,3⟩,⟨.covers 3600,1,6⟩,⟨.covers 2272,1,6⟩,⟨.covers 1376,1,3⟩,⟨.covers 928,1,3⟩,⟨.covers 3232,1,3⟩,⟨.covers 1472,1,3⟩,⟨.covers 2880,1,8⟩,⟨.covers 1920,1,2⟩,⟨.covers 3712,1,3⟩]
def bound : Int := 13

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_006
namespace C13.Global.FastDual53_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,2,9,10]
def points : Finset C13.Point := {1,2,9,10}
def columns : List Code := [247,251,253,254,445,475,499,501,502,505,506,508,637,747,755,757,758,761,762,764,829,885,892,953,956,971,979,985,995,1002,1009,1010,1012,1016,1147,1261,1267,1269,1270,1273,1274,1276,1371,1395,1402,1453,1461,1465,1497,1498,1509,1516,1521,1522,1524,1528,1639,1646,1654,1721,1753,1766,1777,1778,1780,1784,1894,1945,2032,2235,2269,2291,2293,2294,2297,2298,2300,2425,2455,2459,2461,2462,2483,2485,2486,2489,2490,2492,2515,2517,2518,2521,2522,2524,2537,2545,2546,2548,2552,2653,2677,2684,2731,2745,2746,2773,2777,2787,2794,2801,2802,2804,2808,2845,2876,2901,2932,2955,2969,2986,3000,3011,3025,3042,3056,3131,3187,3194,3251,3257,3277,3289,3292,3301,3308,3313,3314,3316,3320,3355,3379,3418,3442,3469,3481,3493,3505,3532,3544,3556,3568,3686,3737,3824]
def rows : List LinearRow := [⟨.covers 519,1,19⟩,⟨.covers 2055,1,19⟩,⟨.covers 43,1,5⟩,⟨.covers 75,1,4⟩,⟨.covers 523,1,4⟩,⟨.covers 1035,1,2⟩,⟨.covers 163,1,1⟩,⟨.covers 1283,1,11⟩,⟨.covers 2563,1,2⟩,⟨.covers 45,1,4⟩,⟨.covers 77,1,4⟩,⟨.covers 525,1,1⟩,⟨.covers 1037,1,5⟩,⟨.covers 53,1,5⟩,⟨.covers 197,1,1⟩,⟨.covers 773,1,5⟩,⟨.covers 3077,1,7⟩,⟨.covers 1073,1,1⟩,⟨.covers 593,1,1⟩,⟨.covers 2145,1,8⟩,⟨.covers 1185,1,3⟩,⟨.covers 705,1,3⟩,⟨.covers 526,1,19⟩,⟨.covers 2062,1,19⟩,⟨.covers 86,1,11⟩,⟨.covers 774,1,19⟩,⟨.covers 2566,1,19⟩,⟨.covers 58,1,4⟩,⟨.covers 778,1,8⟩,⟨.covers 3082,1,4⟩,⟨.covers 1074,1,2⟩,⟨.covers 338,1,1⟩,⟨.covers 2210,1,4⟩,⟨.covers 450,1,1⟩,⟨.covers 2818,1,5⟩,⟨.covers 3330,1,2⟩,⟨.covers 1292,1,3⟩,⟨.covers 2572,1,12⟩,⟨.covers 308,1,2⟩,⟨.covers 564,1,3⟩,⟨.covers 420,1,5⟩,⟨.covers 2820,1,1⟩,⟨.covers 3332,1,5⟩,⟨.covers 184,1,3⟩,⟨.covers 216,1,2⟩,⟨.covers 1112,1,1⟩,⟨.covers 360,1,8⟩,⟨.covers 2152,1,2⟩,⟨.covers 680,1,1⟩,⟨.covers 1224,1,2⟩,⟨.covers 1800,1,19⟩,⟨.covers 3592,1,19⟩,⟨.covers 2224,1,1⟩,⟨.covers 1328,1,3⟩,⟨.covers 2608,1,2⟩,⟨.covers 2256,1,3⟩,⟨.covers 848,1,4⟩,⟨.covers 3152,1,3⟩,⟨.covers 928,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,11⟩,⟨.covers 2880,1,9⟩,⟨.covers 3392,1,8⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source53.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source53.rootCodes link53 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual53_007
