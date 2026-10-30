import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source61
namespace C13.Global.FastDual61_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,10]
def points : Finset C13.Point := {1,3,6,10}
def columns : List Code := [701,743,829,949,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1766,1882,1894,1906,1945,1957,1969,2231,2285,2413,2425,2455,2483,2485,2486,2537,2677,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2773,2789,2861,2869,2873,2876,2901,2917,2921,2929,2951,2963,2965,2966,2979,2981,2982,2985,2986,2988,2993,2994,2996,3000,3011,3013,3025,3041,3127,3251,3253,3277,3292,3308,3379,3418,3493,3505,3532,3544,3623,3635,3686,3725,3737,3749,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 43,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 57,1,1⟩,⟨.covers 1793,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 774,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 2880,1,1⟩,⟨.covers 3648,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source61.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source61.rootCodes link61 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual61_000
namespace C13.Global.FastDual61_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,11]
def points : Finset C13.Point := {1,3,6,11}
def columns : List Code := [701,743,829,949,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1724,1766,1821,1845,1849,1852,1863,1875,1878,1882,1891,1894,1906,1941,1945,1948,1957,1969,1972,1976,1987,1990,2002,2018,2231,2285,2413,2425,2455,2483,2486,2537,2677,2731,2734,2739,2742,2746,2773,2901,2921,2929,2966,2986,2994,3127,3251,3254,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796,3851,3859,3913,3921,3978,3986,4040,4048]
def rows : List LinearRow := [⟨.covers 43,1,2⟩,⟨.covers 525,1,1⟩,⟨.covers 89,1,2⟩,⟨.covers 201,1,2⟩,⟨.covers 46,1,2⟩,⟨.covers 154,1,1⟩,⟨.covers 106,1,2⟩,⟨.covers 202,1,1⟩,⟨.covers 3082,1,2⟩,⟨.covers 92,1,2⟩,⟨.covers 2316,1,2⟩,⟨.covers 1548,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 808,1,1⟩,⟨.covers 3168,1,2⟩,⟨.incident 3,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source61.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source61.rootCodes link61 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual61_001
namespace C13.Global.FastDual61_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,10]
def points : Finset C13.Point := {1,3,7,10}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1371,1374,1395,1398,1402,1461,1509,1639,1651,1654,1693,1721,1753,1882,1894,1906,1945,1957,1969,2413,2421,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2861,2869,2873,2876,2901,2917,2921,2924,2929,2932,2936,2951,2963,2966,2979,2982,2986,2994,3011,3014,3026,3042,3127,3187,3190,3277,3292,3308,3379,3418,3442,3493,3532,3556,3623,3635,3686,3698,3725,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 43,1,15⟩,⟨.covers 75,1,15⟩,⟨.covers 147,1,4⟩,⟨.covers 99,1,5⟩,⟨.covers 579,1,2⟩,⟨.covers 2307,1,2⟩,⟨.covers 45,1,1⟩,⟨.covers 2069,1,2⟩,⟨.covers 57,1,4⟩,⟨.covers 201,1,11⟩,⟨.covers 2121,1,1⟩,⟨.covers 777,1,4⟩,⟨.covers 3089,1,1⟩,⟨.covers 2369,1,3⟩,⟨.covers 1793,1,5⟩,⟨.covers 3329,1,5⟩,⟨.covers 3585,1,1⟩,⟨.covers 46,1,15⟩,⟨.covers 78,1,7⟩,⟨.covers 54,1,2⟩,⟨.covers 198,1,2⟩,⟨.covers 774,1,5⟩,⟨.covers 3078,1,4⟩,⟨.covers 154,1,7⟩,⟨.covers 106,1,10⟩,⟨.covers 202,1,1⟩,⟨.covers 778,1,10⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,15⟩,⟨.covers 114,1,2⟩,⟨.covers 210,1,3⟩,⟨.covers 226,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 2818,1,2⟩,⟨.covers 3586,1,3⟩,⟨.covers 156,1,1⟩,⟨.covers 540,1,1⟩,⟨.covers 108,1,4⟩,⟨.covers 1292,1,8⟩,⟨.covers 2316,1,4⟩,⟨.covers 1548,1,10⟩,⟨.covers 180,1,5⟩,⟨.covers 564,1,3⟩,⟨.covers 2196,1,1⟩,⟨.covers 228,1,5⟩,⟨.covers 1604,1,2⟩,⟨.covers 120,1,4⟩,⟨.covers 184,1,8⟩,⟨.covers 232,1,3⟩,⟨.covers 1800,1,3⟩,⟨.covers 2824,1,4⟩,⟨.covers 2160,1,1⟩,⟨.covers 2256,1,3⟩,⟨.covers 3216,1,7⟩,⟨.covers 2832,1,1⟩,⟨.covers 3600,1,2⟩,⟨.covers 864,1,1⟩,⟨.incident 1,8,-3⟩,⟨.incident 3,8,-7⟩]
def bound : Int := 6

theorem column_mask : listMask columns = restrictMask universeMask Source61.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source61.rootCodes link61 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual61_002
namespace C13.Global.FastDual61_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,11]
def points : Finset C13.Point := {1,3,7,11}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1651,1653,1654,1693,1721,1753,1821,1845,1849,1852,1863,1875,1877,1878,1881,1882,1884,1891,1893,1894,1905,1906,1908,1912,1941,1945,1957,1969,1987,1989,2001,2017,2413,2421,2425,2455,2486,2518,2677,2731,2734,2746,2794,2901,2921,2929,2966,2986,2994,3127,3187,3189,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816,3851,3859,3913,3921,3978,3986,4040,4048]
def rows : List LinearRow := [⟨.covers 39,1,3⟩,⟨.covers 519,1,4⟩,⟨.covers 43,1,17⟩,⟨.covers 75,1,17⟩,⟨.covers 147,1,14⟩,⟨.covers 99,1,3⟩,⟨.covers 45,1,3⟩,⟨.covers 525,1,4⟩,⟨.covers 2061,1,8⟩,⟨.covers 57,1,3⟩,⟨.covers 201,1,4⟩,⟨.covers 2577,1,3⟩,⟨.covers 2337,1,3⟩,⟨.covers 3105,1,3⟩,⟨.covers 2625,1,3⟩,⟨.covers 2817,1,1⟩,⟨.covers 3585,1,3⟩,⟨.covers 46,1,13⟩,⟨.covers 78,1,17⟩,⟨.covers 774,1,10⟩,⟨.covers 2566,1,1⟩,⟨.covers 3078,1,8⟩,⟨.covers 154,1,17⟩,⟨.covers 202,1,17⟩,⟨.covers 114,1,8⟩,⟨.covers 1570,1,3⟩,⟨.covers 3330,1,6⟩,⟨.covers 3586,1,1⟩,⟨.covers 1548,1,10⟩,⟨.covers 2572,1,3⟩,⟨.covers 564,1,1⟩,⟨.covers 2580,1,3⟩,⟨.covers 612,1,1⟩,⟨.covers 2244,1,1⟩,⟨.covers 120,1,8⟩,⟨.covers 216,1,10⟩,⟨.covers 808,1,3⟩,⟨.covers 3336,1,6⟩,⟨.covers 1200,1,11⟩,⟨.covers 2256,1,3⟩,⟨.covers 480,1,11⟩,⟨.covers 2464,1,14⟩,⟨.covers 3232,1,12⟩,⟨.covers 2496,1,7⟩,⟨.covers 2880,1,1⟩,⟨.incident 1,8,-3⟩,⟨.incident 3,8,-3⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source61.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source61.rootCodes link61 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual61_003
namespace C13.Global.FastDual61_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,10]
def points : Finset C13.Point := {1,6,7,10}
def columns : List Code := [829,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1639,1646,1654,1693,1709,1721,1870,1882,1894,1906,1933,1945,1957,1969,2173,2238,2365,2397,2413,2425,2455,2462,2486,2621,2653,2669,2677,2731,2734,2746,2845,2861,2869,2873,2876,2893,2901,2905,2917,2921,2929,2951,2955,2958,2963,2966,2970,2979,2982,2986,2994,3011,3127,3131,3229,3245,3277,3292,3308,3355,3379,3418,3469,3493,3532,3623,3635,3686,3725,3737,3788]
def rows : List LinearRow := [⟨.covers 39,1,4⟩,⟨.covers 71,1,4⟩,⟨.covers 43,1,4⟩,⟨.covers 1283,1,2⟩,⟨.covers 2307,1,2⟩,⟨.covers 77,1,4⟩,⟨.covers 141,1,1⟩,⟨.covers 149,1,5⟩,⟨.covers 101,1,4⟩,⟨.covers 89,1,4⟩,⟨.covers 169,1,2⟩,⟨.covers 297,1,4⟩,⟨.covers 1793,1,5⟩,⟨.covers 142,1,3⟩,⟨.covers 526,1,2⟩,⟨.covers 86,1,12⟩,⟨.covers 166,1,1⟩,⟨.covers 198,1,12⟩,⟨.covers 154,1,4⟩,⟨.covers 202,1,16⟩,⟨.covers 1546,1,10⟩,⟨.covers 210,1,16⟩,⟨.covers 226,1,16⟩,⟨.covers 2818,1,1⟩,⟨.covers 212,1,16⟩,⟨.covers 404,1,1⟩,⟨.covers 2580,1,4⟩,⟨.covers 228,1,8⟩,⟨.covers 420,1,1⟩,⟨.covers 1560,1,2⟩,⟨.covers 680,1,2⟩,⟨.covers 2384,1,4⟩,⟨.covers 1424,1,1⟩,⟨.covers 2704,1,2⟩,⟨.covers 3600,1,4⟩,⟨.covers 1376,1,12⟩,⟨.covers 2656,1,4⟩,⟨.covers 3168,1,8⟩,⟨.covers 2464,1,5⟩,⟨.covers 1696,1,2⟩,⟨.covers 2496,1,6⟩,⟨.covers 1728,1,16⟩,⟨.covers 2880,1,4⟩,⟨.covers 3392,1,8⟩,⟨.covers 3456,1,2⟩,⟨.incident 6,8,-8⟩,⟨.incident 7,8,-4⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source61.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source61.rootCodes link61 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual61_004
namespace C13.Global.FastDual61_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,11]
def points : Finset C13.Point := {1,6,7,11}
def columns : List Code := [829,967,971,979,995,1150,1213,1341,1371,1374,1402,1437,1453,1461,1597,1639,1646,1654,1693,1709,1721,1821,1837,1845,1849,1852,1863,1867,1870,1875,1878,1882,1891,1894,1898,1906,1933,1941,1945,1957,1961,1969,1987,2173,2238,2397,2413,2425,2455,2462,2486,2653,2669,2677,2731,2734,2746,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3165,3181,3277,3292,3308,3351,3379,3405,3433,3478,3532,3627,3635,3661,3669,3754,3788,3851,3859,3913,3921,3978,3986,4040,4048]
def rows : List LinearRow := [⟨.covers 147,1,2⟩,⟨.covers 141,1,1⟩,⟨.covers 197,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 2566,1,2⟩,⟨.covers 154,1,2⟩,⟨.covers 202,1,2⟩,⟨.covers 226,1,2⟩,⟨.covers 212,1,2⟩,⟨.covers 228,1,1⟩,⟨.covers 1412,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 2464,1,2⟩,⟨.covers 1696,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2752,1,1⟩,⟨.incident 7,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source61.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source61.rootCodes link61 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual61_005
namespace C13.Global.FastDual61_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,10,11]
def points : Finset C13.Point := {1,6,10,11}
def columns : List Code := [445,475,701,743,829,925,941,949,953,956,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1465,1498,1639,1646,1654,1693,1709,1717,1721,1766,1870,1882,1894,1906,1933,1945,1957,1969,2173,2231,2235,2238,2269,2285,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2653,2669,2677,2731,2734,2739,2742,2746,2765,2773,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3251,3277,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 523,1,4⟩,⟨.covers 147,1,2⟩,⟨.covers 1283,1,8⟩,⟨.covers 1539,1,6⟩,⟨.covers 77,1,1⟩,⟨.covers 1037,1,4⟩,⟨.covers 197,1,2⟩,⟨.covers 2309,1,5⟩,⟨.covers 1541,1,4⟩,⟨.covers 3077,1,9⟩,⟨.covers 537,1,4⟩,⟨.covers 1289,1,4⟩,⟨.covers 2569,1,2⟩,⟨.covers 3329,1,8⟩,⟨.covers 3585,1,10⟩,⟨.covers 142,1,5⟩,⟨.covers 86,1,10⟩,⟨.covers 1286,1,2⟩,⟨.covers 2566,1,1⟩,⟨.covers 3078,1,7⟩,⟨.covers 554,1,2⟩,⟨.covers 2314,1,2⟩,⟨.covers 1546,1,10⟩,⟨.covers 3082,1,16⟩,⟨.covers 178,1,1⟩,⟨.covers 210,1,2⟩,⟨.covers 2324,1,1⟩,⟨.covers 2580,1,1⟩,⟨.covers 420,1,4⟩,⟨.covers 120,1,2⟩,⟨.covers 2344,1,2⟩,⟨.covers 3336,1,10⟩,⟨.covers 3592,1,8⟩,⟨.covers 2160,1,3⟩,⟨.covers 1200,1,4⟩,⟨.covers 2384,1,1⟩,⟨.covers 1616,1,2⟩,⟨.covers 3152,1,16⟩,⟨.covers 1424,1,4⟩,⟨.covers 2704,1,5⟩,⟨.covers 480,1,4⟩,⟨.covers 1376,1,10⟩,⟨.covers 2656,1,4⟩,⟨.covers 3168,1,7⟩,⟨.covers 2464,1,2⟩,⟨.covers 1696,1,4⟩,⟨.covers 3232,1,9⟩,⟨.covers 1472,1,6⟩,⟨.covers 1728,1,8⟩,⟨.incident 10,8,-8⟩,⟨.incident 11,8,-4⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source61.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source61.rootCodes link61 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual61_006
namespace C13.Global.FastDual61_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,10,11]
def points : Finset C13.Point := {1,7,10,11}
def columns : List Code := [381,471,637,747,829,861,877,885,889,892,967,971,979,995,1143,1147,1150,1213,1245,1261,1371,1374,1395,1398,1402,1437,1453,1461,1485,1509,1639,1646,1651,1654,1658,1693,1709,1721,1741,1753,1870,1882,1894,1906,1933,1945,1957,1969,2173,2238,2397,2413,2421,2425,2455,2462,2486,2518,2653,2669,2677,2681,2731,2734,2746,2794,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3187,3277,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 519,1,4⟩,⟨.covers 1283,1,2⟩,⟨.covers 2307,1,8⟩,⟨.covers 2563,1,8⟩,⟨.covers 141,1,1⟩,⟨.covers 2061,1,4⟩,⟨.covers 533,1,4⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,2⟩,⟨.covers 3077,1,11⟩,⟨.covers 1289,1,5⟩,⟨.covers 2569,1,4⟩,⟨.covers 3329,1,6⟩,⟨.covers 3585,1,8⟩,⟨.covers 46,1,2⟩,⟨.covers 78,1,3⟩,⟨.covers 166,1,8⟩,⟨.covers 550,1,2⟩,⟨.covers 1286,1,4⟩,⟨.covers 3078,1,5⟩,⟨.covers 202,1,4⟩,⟨.covers 2314,1,12⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,16⟩,⟨.covers 114,1,1⟩,⟨.covers 210,1,4⟩,⟨.covers 180,1,2⟩,⟨.covers 420,1,2⟩,⟨.covers 1304,1,1⟩,⟨.covers 1560,1,1⟩,⟨.covers 360,1,4⟩,⟨.covers 3336,1,12⟩,⟨.covers 3592,1,14⟩,⟨.covers 2160,1,4⟩,⟨.covers 1200,1,3⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,5⟩,⟨.covers 3152,1,11⟩,⟨.covers 1424,1,1⟩,⟨.covers 2704,1,12⟩,⟨.covers 3216,1,5⟩,⟨.covers 480,1,4⟩,⟨.covers 2272,1,4⟩,⟨.covers 1376,1,2⟩,⟨.covers 2656,1,4⟩,⟨.covers 1696,1,4⟩,⟨.covers 3232,1,12⟩,⟨.covers 2496,1,4⟩,⟨.covers 1728,1,2⟩,⟨.incident 10,8,-4⟩,⟨.incident 11,8,-8⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source61.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source61.rootCodes link61 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual61_007
