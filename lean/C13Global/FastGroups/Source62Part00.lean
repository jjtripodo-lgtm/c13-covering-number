import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source62
namespace C13.Global.FastDual62_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,5,10]
def points : Finset C13.Point := {1,3,5,10}
def columns : List Code := [254,381,471,508,829,892,956,967,979,981,982,1143,1245,1270,1371,1374,1461,1497,1498,1500,1509,1524,1639,1654,1693,1753,1756,1766,1882,1894,1945,1957,2008,2020,2298,2413,2425,2455,2515,2517,2518,2537,2552,2731,2734,2746,2773,2794,2861,2873,2876,2901,2921,2924,2936,2951,2963,2965,2966,2985,2986,2988,3000,3011,3013,3014,3025,3026,3028,3048,3127,3187,3251,3277,3289,3292,3314,3379,3418,3493,3505,3532,3544,3568,3623,3635,3686,3698,3725,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 135,1,6⟩,⟨.covers 43,1,25⟩,⟨.covers 75,1,6⟩,⟨.covers 147,1,6⟩,⟨.covers 99,1,25⟩,⟨.covers 1283,1,19⟩,⟨.covers 2307,1,6⟩,⟨.covers 526,1,25⟩,⟨.covers 1038,1,6⟩,⟨.covers 774,1,6⟩,⟨.covers 1286,1,19⟩,⟨.covers 3078,1,25⟩,⟨.covers 154,1,6⟩,⟨.covers 778,1,19⟩,⟨.covers 1546,1,6⟩,⟨.covers 3082,1,25⟩,⟨.covers 178,1,19⟩,⟨.covers 402,1,6⟩,⟨.covers 450,1,6⟩,⟨.covers 706,1,6⟩,⟨.covers 2818,1,6⟩,⟨.covers 1584,1,25⟩,⟨.incident 1,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source62.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source62.rootCodes link62 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual62_000
namespace C13.Global.FastDual62_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,5,11]
def points : Finset C13.Point := {1,3,5,11}
def columns : List Code := [254,381,471,508,829,892,956,967,979,981,982,1143,1245,1270,1367,1371,1373,1374,1397,1461,1491,1493,1494,1497,1498,1500,1509,1524,1639,1654,1693,1749,1753,1756,1766,1821,1845,1852,1863,1875,1877,1878,1881,1882,1884,1893,1894,1908,1941,1945,1948,1957,1972,1987,1989,1990,2001,2002,2004,2008,2020,2298,2413,2425,2455,2517,2518,2537,2552,2731,2734,2746,2773,2794,2901,2921,2966,2986,3028,3048,3127,3187,3251,3277,3285,3292,3314,3351,3379,3405,3413,3433,3441,3478,3532,3540,3568,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 135,1,4⟩,⟨.covers 519,1,4⟩,⟨.covers 43,1,16⟩,⟨.covers 75,1,17⟩,⟨.covers 147,1,10⟩,⟨.covers 99,1,9⟩,⟨.covers 45,1,7⟩,⟨.covers 141,1,5⟩,⟨.covers 525,1,2⟩,⟨.covers 57,1,3⟩,⟨.covers 169,1,1⟩,⟨.covers 201,1,9⟩,⟨.covers 2097,1,1⟩,⟨.covers 417,1,4⟩,⟨.covers 1665,1,3⟩,⟨.covers 526,1,17⟩,⟨.covers 1038,1,17⟩,⟨.covers 774,1,3⟩,⟨.covers 3078,1,11⟩,⟨.covers 58,1,1⟩,⟨.covers 2314,1,17⟩,⟨.covers 3082,1,17⟩,⟨.covers 114,1,4⟩,⟨.covers 226,1,3⟩,⟨.covers 706,1,4⟩,⟨.covers 1794,1,7⟩,⟨.covers 3330,1,3⟩,⟨.covers 108,1,4⟩,⟨.covers 1548,1,3⟩,⟨.covers 180,1,1⟩,⟨.covers 564,1,2⟩,⟨.covers 228,1,3⟩,⟨.covers 420,1,5⟩,⟨.covers 184,1,1⟩,⟨.covers 664,1,2⟩,⟨.covers 1800,1,9⟩,⟨.covers 3336,1,14⟩,⟨.covers 1200,1,1⟩,⟨.covers 2352,1,10⟩,⟨.covers 2608,1,12⟩,⟨.covers 2832,1,11⟩,⟨.covers 864,1,4⟩,⟨.covers 2656,1,10⟩,⟨.covers 3648,1,11⟩,⟨.incident 1,8,-3⟩,⟨.incident 3,8,-3⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source62.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source62.rootCodes link62 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual62_001
namespace C13.Global.FastDual62_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,10]
def points : Finset C13.Point := {1,3,6,10}
def columns : List Code := [701,743,829,949,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1766,1882,1894,1906,1945,1957,1969,2231,2285,2413,2425,2455,2483,2485,2486,2537,2677,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2773,2789,2861,2869,2873,2876,2901,2917,2921,2929,2951,2963,2965,2966,2979,2981,2982,2985,2986,2988,2993,2994,2996,3000,3011,3013,3025,3041,3127,3251,3253,3277,3292,3308,3379,3418,3493,3505,3532,3544,3623,3635,3686,3725,3737,3749,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 1031,1,11⟩,⟨.covers 43,1,11⟩,⟨.covers 75,1,5⟩,⟨.covers 147,1,5⟩,⟨.covers 387,1,1⟩,⟨.covers 2307,1,1⟩,⟨.covers 1037,1,11⟩,⟨.covers 2309,1,1⟩,⟨.covers 57,1,5⟩,⟨.covers 89,1,5⟩,⟨.covers 777,1,2⟩,⟨.covers 1793,1,9⟩,⟨.covers 3329,1,10⟩,⟨.covers 46,1,11⟩,⟨.covers 78,1,11⟩,⟨.covers 198,1,2⟩,⟨.covers 774,1,8⟩,⟨.covers 154,1,3⟩,⟨.covers 106,1,11⟩,⟨.covers 778,1,10⟩,⟨.covers 2314,1,1⟩,⟨.covers 3082,1,10⟩,⟨.covers 178,1,4⟩,⟨.covers 210,1,5⟩,⟨.covers 226,1,9⟩,⟨.covers 1794,1,1⟩,⟨.covers 108,1,2⟩,⟨.covers 2316,1,8⟩,⟨.covers 116,1,11⟩,⟨.covers 180,1,2⟩,⟨.covers 308,1,3⟩,⟨.covers 212,1,11⟩,⟨.covers 404,1,3⟩,⟨.covers 184,1,4⟩,⟨.covers 232,1,9⟩,⟨.covers 3600,1,11⟩,⟨.covers 480,1,2⟩,⟨.covers 1824,1,2⟩,⟨.covers 1472,1,3⟩,⟨.covers 2880,1,9⟩,⟨.covers 3648,1,11⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source62.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source62.rootCodes link62 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual62_002
namespace C13.Global.FastDual62_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,11]
def points : Finset C13.Point := {1,3,6,11}
def columns : List Code := [701,743,829,949,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1724,1766,1821,1845,1849,1852,1863,1875,1878,1882,1891,1894,1906,1941,1945,1948,1957,1969,1972,1976,1987,1990,2002,2018,2231,2285,2413,2425,2455,2483,2486,2537,2677,2731,2734,2739,2742,2746,2773,2901,2921,2929,2966,2986,2994,3127,3251,3254,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 43,1,15⟩,⟨.covers 75,1,14⟩,⟨.covers 83,1,1⟩,⟨.covers 147,1,5⟩,⟨.covers 99,1,4⟩,⟨.covers 2307,1,2⟩,⟨.covers 1539,1,2⟩,⟨.covers 525,1,1⟩,⟨.covers 1061,1,2⟩,⟨.covers 57,1,4⟩,⟨.covers 201,1,4⟩,⟨.covers 1161,1,1⟩,⟨.covers 777,1,4⟩,⟨.covers 3081,1,8⟩,⟨.covers 3105,1,1⟩,⟨.covers 449,1,2⟩,⟨.covers 1665,1,3⟩,⟨.covers 3585,1,5⟩,⟨.covers 46,1,15⟩,⟨.covers 78,1,14⟩,⟨.covers 54,1,2⟩,⟨.covers 390,1,2⟩,⟨.covers 774,1,5⟩,⟨.covers 3078,1,4⟩,⟨.covers 154,1,9⟩,⟨.covers 106,1,15⟩,⟨.covers 778,1,10⟩,⟨.covers 3082,1,11⟩,⟨.covers 178,1,2⟩,⟨.covers 226,1,3⟩,⟨.covers 1794,1,2⟩,⟨.covers 3330,1,3⟩,⟨.covers 92,1,1⟩,⟨.covers 156,1,4⟩,⟨.covers 108,1,7⟩,⟨.covers 300,1,1⟩,⟨.covers 2316,1,4⟩,⟨.covers 1548,1,4⟩,⟨.covers 116,1,5⟩,⟨.covers 308,1,3⟩,⟨.covers 228,1,1⟩,⟨.covers 1124,1,1⟩,⟨.covers 184,1,4⟩,⟨.covers 216,1,7⟩,⟨.covers 1800,1,4⟩,⟨.covers 2824,1,5⟩,⟨.covers 3592,1,4⟩,⟨.covers 1200,1,1⟩,⟨.covers 2384,1,5⟩,⟨.covers 912,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 1248,1,2⟩,⟨.covers 1824,1,1⟩,⟨.covers 3360,1,3⟩,⟨.covers 2496,1,7⟩,⟨.covers 2752,1,4⟩,⟨.incident 1,8,-3⟩,⟨.incident 3,8,-7⟩]
def bound : Int := 6

theorem column_mask : listMask columns = restrictMask universeMask Source62.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source62.rootCodes link62 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual62_003
namespace C13.Global.FastDual62_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,5,6,10]
def points : Finset C13.Point := {1,5,6,10}
def columns : List Code := [445,475,829,925,941,956,967,971,979,1371,1374,1437,1453,1461,1498,1639,1646,1654,1693,1766,1870,1882,1894,1933,1945,1957,2235,2269,2365,2397,2413,2425,2455,2459,2461,2462,2477,2489,2509,2521,2537,2653,2717,2731,2734,2746,2765,2773,2845,2861,2873,2876,2893,2901,2905,2921,2951,2955,2957,2958,2963,2965,2966,2969,2970,2972,2985,2986,2988,3000,3011,3013,3017,3025,3127,3131,3229,3251,3277,3292,3355,3379,3418,3469,3481,3493,3505,3532,3544,3623,3635,3686,3725,3737,3788]
def rows : List LinearRow := [⟨.covers 39,1,3⟩,⟨.covers 135,1,11⟩,⟨.covers 523,1,11⟩,⟨.covers 1283,1,11⟩,⟨.covers 1037,1,11⟩,⟨.covers 53,1,8⟩,⟨.covers 101,1,8⟩,⟨.covers 142,1,11⟩,⟨.covers 1286,1,3⟩,⟨.covers 58,1,11⟩,⟨.covers 106,1,11⟩,⟨.covers 114,1,11⟩,⟨.covers 210,1,11⟩,⟨.covers 226,1,5⟩,⟨.covers 92,1,8⟩,⟨.covers 180,1,3⟩,⟨.covers 212,1,3⟩,⟨.covers 788,1,3⟩,⟨.covers 2580,1,3⟩,⟨.covers 120,1,11⟩,⟨.covers 232,1,11⟩,⟨.covers 1808,1,11⟩,⟨.covers 3600,1,11⟩,⟨.covers 1376,1,8⟩,⟨.covers 3168,1,11⟩,⟨.covers 928,1,5⟩,⟨.covers 1696,1,5⟩,⟨.covers 3232,1,11⟩,⟨.covers 2848,1,5⟩,⟨.covers 2752,1,5⟩,⟨.covers 2880,1,5⟩,⟨.covers 3392,1,11⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source62.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source62.rootCodes link62 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual62_004
namespace C13.Global.FastDual62_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,5,6,11]
def points : Finset C13.Point := {1,5,6,11}
def columns : List Code := [445,475,829,925,941,956,967,971,979,1341,1371,1374,1437,1453,1461,1498,1639,1646,1654,1693,1766,1821,1837,1845,1852,1863,1867,1870,1875,1878,1882,1894,1933,1941,1945,1948,1957,1964,1972,1987,1990,1994,2002,2235,2269,2397,2413,2425,2455,2462,2509,2537,2653,2731,2734,2746,2765,2773,2893,2901,2921,2958,2966,2986,3127,3131,3165,3251,3277,3292,3351,3379,3405,3433,3478,3532,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 135,1,1⟩,⟨.covers 83,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 58,1,1⟩,⟨.covers 114,1,2⟩,⟨.covers 226,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 120,1,2⟩,⟨.covers 232,1,2⟩,⟨.covers 2608,1,1⟩,⟨.covers 2832,1,1⟩,⟨.covers 864,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 2848,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 2752,1,1⟩,⟨.incident 5,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source62.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source62.rootCodes link62 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual62_005
namespace C13.Global.FastDual62_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,5,6,10]
def points : Finset C13.Point := {3,5,6,10}
def columns : List Code := [702,727,829,830,855,919,956,967,979,1207,1246,1335,1371,1374,1447,1461,1498,1591,1639,1654,1691,1693,1703,1766,1819,1831,1882,1894,1945,1957,2411,2413,2425,2455,2537,2647,2711,2731,2734,2746,2759,2773,2839,2859,2861,2862,2873,2874,2876,2887,2899,2901,2921,2951,2963,2965,2966,2985,2986,2988,3000,3011,3013,3025,3127,3239,3251,3277,3278,3292,3367,3379,3406,3418,3493,3505,3532,3544,3623,3635,3686,3725,3737,3788]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 71,1,4⟩,⟨.covers 75,1,4⟩,⟨.covers 139,1,4⟩,⟨.covers 83,1,4⟩,⟨.covers 163,1,2⟩,⟨.covers 387,1,4⟩,⟨.covers 525,1,2⟩,⟨.covers 53,1,5⟩,⟨.covers 101,1,9⟩,⟨.covers 197,1,4⟩,⟨.covers 1541,1,2⟩,⟨.covers 1289,1,4⟩,⟨.covers 3329,1,3⟩,⟨.covers 46,1,5⟩,⟨.covers 58,1,2⟩,⟨.covers 106,1,12⟩,⟨.covers 202,1,10⟩,⟨.covers 2186,1,2⟩,⟨.covers 114,1,8⟩,⟨.covers 2098,1,2⟩,⟨.covers 226,1,16⟩,⟨.covers 3330,1,2⟩,⟨.covers 92,1,2⟩,⟨.covers 108,1,7⟩,⟨.covers 172,1,1⟩,⟨.covers 1292,1,10⟩,⟨.covers 308,1,1⟩,⟨.covers 2580,1,4⟩,⟨.covers 420,1,1⟩,⟨.covers 120,1,16⟩,⟨.covers 232,1,16⟩,⟨.covers 2824,1,1⟩,⟨.covers 1328,1,1⟩,⟨.covers 2608,1,2⟩,⟨.covers 848,1,4⟩,⟨.covers 1616,1,8⟩,⟨.covers 3152,1,10⟩,⟨.covers 3600,1,4⟩,⟨.covers 1376,1,16⟩,⟨.covers 3168,1,8⟩,⟨.covers 928,1,5⟩,⟨.covers 3232,1,4⟩,⟨.covers 1472,1,2⟩,⟨.covers 2752,1,4⟩,⟨.covers 2880,1,4⟩,⟨.covers 3648,1,8⟩,⟨.incident 5,8,-4⟩,⟨.incident 6,8,-8⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source62.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source62.rootCodes link62 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual62_006
