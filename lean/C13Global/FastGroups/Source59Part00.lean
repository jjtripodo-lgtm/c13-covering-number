import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source59
namespace C13.Global.FastDual59_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,5,10]
def points : Finset C13.Point := {2,3,5,10}
def columns : List Code := [254,508,829,830,892,956,979,1243,1255,1270,1371,1447,1461,1497,1498,1509,1524,1639,1654,1691,1753,1754,1766,1819,1831,1882,1894,1945,1957,2008,2020,2263,2283,2298,2411,2425,2455,2515,2517,2518,2537,2552,2647,2731,2746,2771,2773,2774,2794,2839,2859,2873,2874,2876,2899,2901,2902,2921,2922,2936,2963,2965,2966,2985,2986,3000,3011,3025,3026,3028,3048,3187,3251,3277,3278,3289,3290,3292,3314,3379,3418,3493,3505,3532,3544,3568,3635,3686,3698,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 77,1,2⟩,⟨.covers 53,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,2⟩,⟨.covers 526,1,2⟩,⟨.covers 1038,1,1⟩,⟨.covers 1286,1,2⟩,⟨.covers 3078,1,1⟩,⟨.covers 172,1,2⟩,⟨.covers 2572,1,1⟩,⟨.covers 596,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3332,1,2⟩,⟨.covers 3588,1,1⟩,⟨.covers 1696,1,2⟩,⟨.incident 2,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source59.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source59.rootCodes link59 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual59_000
namespace C13.Global.FastDual59_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,5,11]
def points : Finset C13.Point := {2,3,5,11}
def columns : List Code := [254,508,829,830,892,956,979,1243,1255,1270,1371,1447,1461,1491,1497,1498,1509,1524,1639,1654,1691,1747,1753,1754,1766,1819,1831,1845,1846,1852,1875,1881,1882,1893,1894,1908,1939,1945,1946,1957,1958,1972,1987,2001,2002,2008,2020,2263,2283,2298,2411,2425,2455,2517,2518,2537,2552,2647,2731,2746,2773,2774,2794,2839,2859,2901,2921,2966,2986,3028,3048,3187,3251,3277,3278,3285,3286,3292,3314,3379,3433,3441,3478,3532,3540,3568,3635,3669,3754,3762,3788,3796,3853,3861,3881,3889,3980,3988,4008,4016]
def rows : List LinearRow := [⟨.covers 45,1,17⟩,⟨.covers 77,1,33⟩,⟨.covers 57,1,17⟩,⟨.covers 89,1,17⟩,⟨.covers 169,1,33⟩,⟨.covers 526,1,33⟩,⟨.covers 1038,1,17⟩,⟨.covers 2314,1,33⟩,⟨.covers 1546,1,17⟩,⟨.covers 3082,1,17⟩,⟨.covers 92,1,33⟩,⟨.covers 2572,1,33⟩,⟨.covers 664,1,17⟩,⟨.covers 1352,1,17⟩,⟨.covers 2656,1,33⟩,⟨.incident 3,8,-33⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source59.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source59.rootCodes link59 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual59_001
namespace C13.Global.FastDual59_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,10]
def points : Finset C13.Point := {2,3,7,10}
def columns : List Code := [379,439,631,699,823,827,829,830,883,885,886,889,890,892,947,979,995,1371,1395,1402,1447,1461,1509,1639,1651,1654,1691,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2411,2419,2425,2426,2455,2486,2518,2647,2675,2677,2678,2731,2746,2794,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2902,2915,2921,2922,2929,2930,2932,2936,2963,2966,2979,2986,2994,3011,3026,3042,3187,3277,3278,3292,3308,3379,3418,3442,3493,3532,3556,3635,3686,3698,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 135,1,11⟩,⟨.covers 75,1,3⟩,⟨.covers 45,1,11⟩,⟨.covers 77,1,11⟩,⟨.covers 101,1,8⟩,⟨.covers 89,1,8⟩,⟨.covers 169,1,11⟩,⟨.covers 2369,1,3⟩,⟨.covers 2625,1,3⟩,⟨.covers 3329,1,11⟩,⟨.covers 3585,1,11⟩,⟨.covers 46,1,11⟩,⟨.covers 78,1,5⟩,⟨.covers 2566,1,5⟩,⟨.covers 2314,1,5⟩,⟨.covers 1546,1,11⟩,⟨.covers 3082,1,5⟩,⟨.covers 210,1,11⟩,⟨.covers 226,1,11⟩,⟨.covers 92,1,11⟩,⟨.covers 172,1,8⟩,⟨.covers 1292,1,11⟩,⟨.covers 1548,1,3⟩,⟨.covers 228,1,3⟩,⟨.covers 1796,1,11⟩,⟨.covers 2820,1,5⟩,⟨.covers 3588,1,5⟩,⟨.covers 2824,1,5⟩,⟨.covers 1136,1,11⟩,⟨.covers 2224,1,11⟩,⟨.covers 1424,1,11⟩,⟨.covers 1728,1,3⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source59.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source59.rootCodes link59 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual59_002
namespace C13.Global.FastDual59_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,11]
def points : Finset C13.Point := {2,3,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,883,885,886,889,890,892,947,979,995,1371,1395,1401,1402,1447,1461,1509,1639,1651,1653,1654,1691,1721,1753,1819,1831,1843,1845,1846,1849,1850,1852,1875,1881,1882,1891,1893,1894,1905,1906,1908,1912,1939,1945,1955,1957,1969,1987,2001,2017,2411,2419,2425,2455,2486,2518,2647,2675,2677,2731,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3187,3277,3278,3292,3308,3379,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816,3853,3861,3881,3889,3980,3988,4008,4016]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 1031,1,4⟩,⟨.covers 2055,1,3⟩,⟨.covers 75,1,2⟩,⟨.covers 1035,1,5⟩,⟨.covers 2059,1,6⟩,⟨.covers 45,1,20⟩,⟨.covers 77,1,20⟩,⟨.covers 149,1,11⟩,⟨.covers 101,1,3⟩,⟨.covers 89,1,3⟩,⟨.covers 169,1,3⟩,⟨.covers 2369,1,2⟩,⟨.covers 46,1,20⟩,⟨.covers 78,1,18⟩,⟨.covers 1286,1,10⟩,⟨.covers 2566,1,9⟩,⟨.covers 3078,1,2⟩,⟨.covers 2314,1,2⟩,⟨.covers 1546,1,8⟩,⟨.covers 210,1,1⟩,⟨.covers 3090,1,2⟩,⟨.covers 1122,1,3⟩,⟨.covers 2210,1,3⟩,⟨.covers 3106,1,1⟩,⟨.covers 898,1,3⟩,⟨.covers 156,1,20⟩,⟨.covers 108,1,2⟩,⟨.covers 172,1,12⟩,⟨.covers 116,1,9⟩,⟨.covers 180,1,3⟩,⟨.covers 228,1,6⟩,⟨.covers 1604,1,1⟩,⟨.covers 2820,1,2⟩,⟨.covers 3588,1,10⟩,⟨.covers 120,1,8⟩,⟨.covers 184,1,10⟩,⟨.covers 1352,1,2⟩,⟨.covers 2824,1,4⟩,⟨.covers 3336,1,4⟩,⟨.covers 848,1,2⟩,⟨.covers 1616,1,1⟩,⟨.covers 3600,1,2⟩,⟨.covers 480,1,3⟩,⟨.covers 2656,1,2⟩,⟨.covers 3360,1,3⟩,⟨.covers 3616,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 2496,1,13⟩,⟨.covers 1728,1,2⟩,⟨.covers 2752,1,8⟩,⟨.incident 2,8,-8⟩,⟨.incident 3,8,-6⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source59.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source59.rootCodes link59 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual59_003
namespace C13.Global.FastDual59_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,10,11]
def points : Finset C13.Point := {2,3,10,11}
def columns : List Code := [247,251,253,254,379,439,499,501,502,505,506,508,631,699,755,757,758,761,762,764,823,827,829,830,883,885,886,889,890,892,947,949,950,953,954,956,979,995,1009,1010,1012,1016,1243,1255,1267,1269,1270,1273,1274,1276,1371,1395,1402,1447,1459,1461,1497,1498,1509,1510,1521,1522,1524,1528,1639,1651,1654,1691,1715,1721,1753,1754,1765,1766,1777,1778,1780,1784,1819,1831,1843,1882,1894,1906,1945,1957,1969,2008,2020,2032,2263,2283,2291,2293,2294,2297,2298,2300,2411,2419,2425,2455,2483,2486,2517,2518,2537,2538,2545,2546,2548,2552,2647,2675,2677,2731,2739,2746,2773,2774,2793,2794,2801,2802,2804,2808,2839,2859,2867,2901,2921,2929,2966,2986,2994,3028,3048,3056,3187,3251,3277,3278,3292,3308,3313,3314,3316,3320,3379,3532,3568,3635,3788,3824]
def rows : List LinearRow := [⟨.covers 71,1,4⟩,⟨.covers 135,1,4⟩,⟨.covers 1031,1,1⟩,⟨.covers 2055,1,5⟩,⟨.covers 75,1,5⟩,⟨.covers 139,1,4⟩,⟨.covers 1035,1,4⟩,⟨.covers 2059,1,2⟩,⟨.covers 525,1,19⟩,⟨.covers 1037,1,19⟩,⟨.covers 149,1,1⟩,⟨.covers 101,1,5⟩,⟨.covers 2309,1,7⟩,⟨.covers 1541,1,5⟩,⟨.covers 89,1,1⟩,⟨.covers 1289,1,2⟩,⟨.covers 2569,1,11⟩,⟨.covers 2129,1,3⟩,⟨.covers 1169,1,3⟩,⟨.covers 2145,1,1⟩,⟨.covers 1185,1,1⟩,⟨.covers 449,1,8⟩,⟨.covers 3329,1,19⟩,⟨.covers 3585,1,19⟩,⟨.covers 526,1,19⟩,⟨.covers 1038,1,19⟩,⟨.covers 1286,1,12⟩,⟨.covers 2566,1,3⟩,⟨.covers 106,1,4⟩,⟨.covers 2314,1,4⟩,⟨.covers 1546,1,8⟩,⟨.covers 114,1,3⟩,⟨.covers 178,1,2⟩,⟨.covers 1106,1,1⟩,⟨.covers 2194,1,2⟩,⟨.covers 2210,1,1⟩,⟨.covers 450,1,2⟩,⟨.covers 706,1,8⟩,⟨.covers 108,1,7⟩,⟨.covers 172,1,4⟩,⟨.covers 1292,1,19⟩,⟨.covers 1548,1,19⟩,⟨.covers 596,1,5⟩,⟨.covers 612,1,2⟩,⟨.covers 1124,1,3⟩,⟨.covers 1796,1,1⟩,⟨.covers 2820,1,5⟩,⟨.covers 344,1,4⟩,⟨.covers 664,1,1⟩,⟨.covers 2152,1,2⟩,⟨.covers 680,1,1⟩,⟨.covers 1800,1,5⟩,⟨.covers 2824,1,2⟩,⟨.covers 368,1,1⟩,⟨.covers 432,1,3⟩,⟨.covers 1616,1,1⟩,⟨.covers 3152,1,11⟩,⟨.covers 2704,1,1⟩,⟨.covers 1376,1,2⟩,⟨.covers 2656,1,3⟩,⟨.covers 2464,1,3⟩,⟨.covers 1696,1,4⟩,⟨.covers 1920,1,9⟩,⟨.covers 2944,1,8⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source59.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source59.rootCodes link59 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual59_004
namespace C13.Global.FastDual59_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,5,7,10]
def points : Finset C13.Point := {2,5,7,10}
def columns : List Code := [638,731,829,830,859,892,923,971,979,1371,1447,1453,1461,1509,1627,1639,1646,1654,1691,1753,1819,1831,1882,1894,1945,1957,2171,2270,2363,2395,2411,2425,2455,2462,2518,2619,2647,2651,2653,2654,2667,2682,2715,2731,2746,2763,2778,2794,2839,2843,2845,2846,2859,2873,2874,2876,2891,2899,2901,2902,2905,2906,2908,2921,2922,2936,2955,2963,2966,2970,2986,3011,3018,3026,3131,3163,3187,3277,3278,3292,3355,3379,3418,3469,3493,3532,3611,3635,3662,3674,3686,3698,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 135,1,1⟩,⟨.covers 43,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 57,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 1038,1,1⟩,⟨.covers 54,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3344,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 1696,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 2848,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 1728,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source59.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source59.rootCodes link59 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual59_005
namespace C13.Global.FastDual59_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,5,7,11]
def points : Finset C13.Point := {2,5,7,11}
def columns : List Code := [638,731,829,830,859,892,923,971,979,1371,1447,1453,1461,1509,1627,1639,1646,1654,1691,1739,1753,1819,1831,1837,1838,1845,1846,1852,1867,1875,1881,1882,1893,1894,1900,1908,1931,1939,1945,1957,1987,1993,2001,2171,2270,2363,2411,2425,2455,2462,2518,2619,2647,2653,2667,2731,2746,2794,2839,2859,2901,2921,2966,2986,3131,3179,3187,3277,3278,3292,3371,3379,3433,3441,3470,3478,3532,3540,3627,3635,3661,3669,3754,3788,3853,3861,3881,3889,3980,3988,4008,4016]
def rows : List LinearRow := [⟨.covers 147,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 197,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 928,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 1728,1,1⟩,⟨.incident 7,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source59.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source59.rootCodes link59 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual59_006
namespace C13.Global.FastDual59_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,5,10,11]
def points : Finset C13.Point := {2,5,10,11}
def columns : List Code := [254,445,475,508,638,731,829,830,859,892,923,956,971,979,985,986,1243,1255,1270,1371,1435,1447,1453,1461,1497,1498,1509,1524,1627,1639,1646,1654,1691,1753,1754,1766,1819,1831,1882,1894,1945,1957,2008,2020,2171,2235,2263,2269,2270,2283,2298,2363,2411,2425,2455,2462,2475,2517,2518,2524,2537,2552,2619,2647,2653,2667,2731,2746,2773,2774,2780,2794,2839,2859,2901,2921,2966,2986,3028,3048,3131,3187,3251,3277,3278,3292,3314,3379,3532,3568,3635,3788]
def rows : List LinearRow := [⟨.covers 1035,1,6⟩,⟨.covers 101,1,25⟩,⟨.covers 3077,1,25⟩,⟨.covers 1289,1,6⟩,⟨.covers 1169,1,6⟩,⟨.covers 3329,1,25⟩,⟨.covers 3585,1,25⟩,⟨.covers 1038,1,19⟩,⟨.covers 1286,1,25⟩,⟨.covers 3078,1,6⟩,⟨.covers 1546,1,6⟩,⟨.covers 1292,1,19⟩,⟨.covers 3332,1,6⟩,⟨.covers 3588,1,25⟩,⟨.covers 1112,1,6⟩,⟨.covers 1176,1,6⟩,⟨.covers 1800,1,6⟩,⟨.covers 1136,1,19⟩,⟨.covers 1616,1,6⟩,⟨.covers 1696,1,25⟩,⟨.covers 3232,1,6⟩,⟨.incident 10,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source59.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source59.rootCodes link59 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual59_007
