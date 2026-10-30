import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source64
namespace C13.Global.FastDual64_024
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,9]
def points : Finset C13.Point := {2,3,7,9}
def columns : List Code := [379,439,631,699,829,830,885,886,892,979,995,1371,1395,1401,1402,1447,1461,1509,1639,1653,1654,1691,1721,1753,1852,1894,1908,1945,1987,2001,2411,2419,2425,2426,2455,2486,2518,2647,2677,2678,2731,2746,2794,2876,2901,2932,2986,3011,3042,3187,3277,3278,3292,3308,3379,3403,3411,3417,3418,3427,3433,3434,3441,3442,3448,3463,3477,3478,3493,3494,3508,3525,3526,3532,3540,3556,3655,3669,3686,3700,3723,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 45,1,8⟩,⟨.covers 77,1,11⟩,⟨.covers 149,1,2⟩,⟨.covers 101,1,2⟩,⟨.covers 1061,1,1⟩,⟨.covers 2309,1,2⟩,⟨.covers 1541,1,1⟩,⟨.covers 89,1,5⟩,⟨.covers 169,1,12⟩,⟨.covers 2089,1,2⟩,⟨.covers 201,1,7⟩,⟨.covers 777,1,10⟩,⟨.covers 1289,1,5⟩,⟨.covers 2577,1,1⟩,⟨.covers 225,1,2⟩,⟨.covers 2145,1,1⟩,⟨.covers 2337,1,1⟩,⟨.covers 2817,1,2⟩,⟨.covers 3585,1,1⟩,⟨.covers 46,1,18⟩,⟨.covers 78,1,8⟩,⟨.covers 86,1,4⟩,⟨.covers 166,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 1286,1,4⟩,⟨.covers 2566,1,1⟩,⟨.covers 1050,1,2⟩,⟨.covers 106,1,5⟩,⟨.covers 202,1,8⟩,⟨.covers 2314,1,5⟩,⟨.covers 1546,1,12⟩,⟨.covers 1106,1,1⟩,⟨.covers 2194,1,1⟩,⟨.covers 1298,1,1⟩,⟨.covers 1570,1,1⟩,⟨.covers 156,1,18⟩,⟨.covers 108,1,13⟩,⟨.covers 172,1,5⟩,⟨.covers 2316,1,13⟩,⟨.covers 1548,1,18⟩,⟨.covers 2572,1,5⟩,⟨.covers 180,1,2⟩,⟨.covers 3588,1,2⟩,⟨.covers 120,1,5⟩,⟨.covers 184,1,2⟩,⟨.covers 3336,1,5⟩,⟨.covers 3592,1,1⟩,⟨.covers 2704,1,11⟩,⟨.covers 2656,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 1728,1,2⟩,⟨.incident 2,8,-4⟩,⟨.incident 3,8,-12⟩]
def bound : Int := 3

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_024
namespace C13.Global.FastDual64_025
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,7,10]
def points : Finset C13.Point := {2,3,7,10}
def columns : List Code := [379,439,631,699,823,827,829,830,883,885,886,889,890,892,947,979,995,1371,1395,1402,1447,1461,1509,1639,1651,1654,1691,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2411,2419,2425,2426,2455,2486,2518,2647,2675,2677,2678,2731,2746,2794,2839,2859,2867,2869,2870,2873,2874,2876,2899,2901,2902,2915,2921,2922,2929,2930,2932,2936,2963,2966,2979,2986,2994,3011,3026,3042,3187,3277,3278,3292,3308,3379,3418,3442,3493,3532,3556,3635,3686,3698,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 209,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 2224,1,1⟩,⟨.covers 736,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_025
namespace C13.Global.FastDual64_026
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,5,7,9]
def points : Finset C13.Point := {2,5,7,9}
def columns : List Code := [638,731,829,830,892,923,971,979,1371,1447,1453,1461,1509,1639,1646,1654,1691,1739,1753,1838,1852,1894,1908,1931,1945,1987,2001,2171,2270,2363,2395,2411,2425,2455,2462,2518,2647,2653,2715,2731,2746,2763,2794,2845,2876,2901,2955,2986,3011,3131,3163,3179,3187,3277,3278,3292,3355,3371,3379,3385,3403,3411,3417,3418,3427,3433,3441,3463,3469,3470,3477,3478,3484,3493,3525,3526,3532,3540,3655,3669,3686,3723,3737,3754]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 43,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 53,1,1⟩,⟨.covers 57,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 329,1,1⟩,⟨.covers 177,1,1⟩,⟨.covers 225,1,2⟩,⟨.covers 166,1,1⟩,⟨.covers 774,1,2⟩,⟨.covers 2566,1,1⟩,⟨.covers 3090,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 108,1,2⟩,⟨.covers 2820,1,1⟩,⟨.covers 184,1,2⟩,⟨.covers 232,1,2⟩,⟨.covers 2352,1,1⟩,⟨.covers 1584,1,2⟩,⟨.covers 3600,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 1696,1,2⟩,⟨.covers 2848,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 1728,1,1⟩,⟨.incident 5,8,-1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_026
namespace C13.Global.FastDual64_027
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,5,7,10]
def points : Finset C13.Point := {2,5,7,10}
def columns : List Code := [638,731,829,830,859,892,923,971,979,1371,1447,1453,1461,1509,1627,1639,1646,1654,1691,1753,1819,1831,1882,1894,1945,1957,2171,2270,2363,2395,2411,2425,2455,2462,2518,2619,2647,2651,2653,2654,2667,2682,2715,2731,2746,2763,2778,2794,2839,2843,2845,2846,2859,2873,2874,2876,2891,2899,2901,2902,2905,2906,2908,2921,2922,2936,2955,2963,2966,2970,2986,3011,3018,3026,3131,3163,3187,3277,3278,3292,3355,3379,3418,3469,3493,3532,3611,3635,3662,3674,3686,3698,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 71,1,7⟩,⟨.covers 135,1,7⟩,⟨.covers 519,1,4⟩,⟨.covers 43,1,5⟩,⟨.covers 139,1,5⟩,⟨.covers 1035,1,2⟩,⟨.covers 147,1,4⟩,⟨.covers 163,1,1⟩,⟨.covers 323,1,3⟩,⟨.covers 77,1,4⟩,⟨.covers 2061,1,7⟩,⟨.covers 57,1,4⟩,⟨.covers 329,1,3⟩,⟨.covers 113,1,2⟩,⟨.covers 177,1,11⟩,⟨.covers 209,1,2⟩,⟨.covers 225,1,11⟩,⟨.covers 3585,1,9⟩,⟨.covers 46,1,3⟩,⟨.covers 1038,1,7⟩,⟨.covers 166,1,3⟩,⟨.covers 198,1,4⟩,⟨.covers 774,1,7⟩,⟨.covers 156,1,7⟩,⟨.covers 172,1,11⟩,⟨.covers 2316,1,4⟩,⟨.covers 116,1,7⟩,⟨.covers 3588,1,4⟩,⟨.covers 184,1,11⟩,⟨.covers 232,1,11⟩,⟨.covers 1352,1,1⟩,⟨.covers 1800,1,9⟩,⟨.covers 1136,1,2⟩,⟨.covers 2352,1,2⟩,⟨.covers 1584,1,2⟩,⟨.covers 1232,1,2⟩,⟨.covers 848,1,1⟩,⟨.covers 2384,1,1⟩,⟨.covers 912,1,2⟩,⟨.covers 3216,1,2⟩,⟨.covers 3344,1,9⟩,⟨.covers 864,1,3⟩,⟨.covers 3168,1,7⟩,⟨.covers 2464,1,4⟩,⟨.covers 1696,1,11⟩,⟨.covers 3232,1,7⟩,⟨.covers 2848,1,5⟩,⟨.covers 2496,1,6⟩,⟨.covers 1728,1,7⟩,⟨.covers 2944,1,2⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_027
namespace C13.Global.FastDual64_028
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,5,7,10]
def points : Finset C13.Point := {3,5,7,10}
def columns : List Code := [381,471,829,830,855,892,919,967,979,1143,1245,1335,1371,1374,1383,1447,1461,1509,1591,1639,1654,1691,1693,1753,1819,1831,1882,1894,1945,1957,2391,2411,2413,2425,2455,2503,2518,2647,2731,2734,2746,2794,2839,2859,2861,2862,2873,2874,2876,2887,2899,2901,2902,2921,2922,2924,2936,2951,2963,2966,2986,3011,3014,3026,3127,3175,3187,3277,3278,3292,3367,3379,3406,3418,3493,3532,3623,3635,3686,3698,3725,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 135,1,4⟩,⟨.covers 75,1,6⟩,⟨.covers 147,1,4⟩,⟨.covers 99,1,1⟩,⟨.covers 163,1,10⟩,⟨.covers 579,1,4⟩,⟨.covers 45,1,4⟩,⟨.covers 2061,1,1⟩,⟨.covers 57,1,3⟩,⟨.covers 169,1,6⟩,⟨.covers 201,1,1⟩,⟨.covers 2121,1,1⟩,⟨.covers 3081,1,8⟩,⟨.covers 177,1,13⟩,⟨.covers 2097,1,1⟩,⟨.covers 2129,1,1⟩,⟨.covers 225,1,14⟩,⟨.covers 3585,1,3⟩,⟨.covers 78,1,6⟩,⟨.covers 142,1,3⟩,⟨.covers 54,1,6⟩,⟨.covers 198,1,4⟩,⟨.covers 58,1,1⟩,⟨.covers 154,1,3⟩,⟨.covers 1546,1,6⟩,⟨.covers 156,1,11⟩,⟨.covers 540,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 172,1,13⟩,⟨.covers 2324,1,4⟩,⟨.covers 1604,1,1⟩,⟨.covers 184,1,11⟩,⟨.covers 232,1,15⟩,⟨.covers 2824,1,1⟩,⟨.covers 2352,1,1⟩,⟨.covers 1584,1,1⟩,⟨.covers 912,1,4⟩,⟨.covers 1424,1,3⟩,⟨.covers 3216,1,1⟩,⟨.covers 3344,1,6⟩,⟨.covers 864,1,6⟩,⟨.covers 1376,1,1⟩,⟨.covers 3168,1,4⟩,⟨.covers 928,1,10⟩,⟨.covers 3232,1,7⟩,⟨.covers 3616,1,3⟩,⟨.covers 2496,1,4⟩,⟨.covers 1728,1,11⟩,⟨.covers 1920,1,6⟩,⟨.covers 2944,1,4⟩,⟨.covers 3456,1,8⟩,⟨.incident 5,8,-3⟩,⟨.incident 7,8,-7⟩]
def bound : Int := 6

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_028
