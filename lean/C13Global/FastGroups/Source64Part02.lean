import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source64
namespace C13.Global.FastDual64_016
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,9,10]
def points : Finset C13.Point := {0,3,9,10}
def columns : List Code := [247,251,253,254,382,487,499,501,502,505,506,508,702,727,755,757,758,761,762,764,830,886,892,954,956,967,979,981,995,998,1009,1010,1012,1016,1207,1246,1267,1269,1270,1273,1274,1276,1374,1398,1402,1447,1459,1461,1498,1500,1509,1510,1521,1522,1524,1528,1654,1691,1693,1721,1753,1766,1777,1778,1780,1784,1894,1945,2032,2167,2286,2291,2293,2294,2297,2298,2300,2407,2411,2413,2414,2419,2421,2422,2425,2426,2428,2486,2518,2531,2533,2534,2537,2538,2540,2545,2546,2548,2552,2647,2677,2678,2734,2746,2748,2771,2773,2790,2794,2801,2802,2804,2808,2862,2876,2887,2901,2918,2932,2986,3000,3011,3025,3042,3056,3127,3187,3190,3251,3253,3278,3290,3292,3302,3308,3313,3314,3316,3320,3367,3379,3406,3418,3430,3442,3493,3505,3532,3544,3556,3568,3686,3737,3824]
def rows : List LinearRow := [⟨.covers 135,1,9⟩,⟨.covers 519,1,5⟩,⟨.covers 1031,1,1⟩,⟨.covers 523,1,19⟩,⟨.covers 2059,1,19⟩,⟨.covers 83,1,1⟩,⟨.covers 163,1,4⟩,⟨.covers 1283,1,5⟩,⟨.covers 2563,1,8⟩,⟨.covers 525,1,19⟩,⟨.covers 2061,1,19⟩,⟨.covers 53,1,2⟩,⟨.covers 773,1,2⟩,⟨.covers 3077,1,12⟩,⟨.covers 57,1,11⟩,⟨.covers 777,1,19⟩,⟨.covers 2569,1,19⟩,⟨.covers 1073,1,3⟩,⟨.covers 2129,1,1⟩,⟨.covers 417,1,1⟩,⟨.covers 449,1,3⟩,⟨.covers 2817,1,4⟩,⟨.covers 3329,1,1⟩,⟨.covers 142,1,8⟩,⟨.covers 526,1,2⟩,⟨.covers 1038,1,5⟩,⟨.covers 58,1,3⟩,⟨.covers 202,1,1⟩,⟨.covers 778,1,11⟩,⟨.covers 3082,1,3⟩,⟨.covers 1074,1,2⟩,⟨.covers 1106,1,5⟩,⟨.covers 2194,1,8⟩,⟨.covers 674,1,1⟩,⟨.covers 706,1,1⟩,⟨.covers 172,1,3⟩,⟨.covers 1292,1,7⟩,⟨.covers 2572,1,4⟩,⟨.covers 116,1,4⟩,⟨.covers 596,1,4⟩,⟨.covers 404,1,8⟩,⟨.covers 2196,1,2⟩,⟨.covers 1796,1,19⟩,⟨.covers 3588,1,19⟩,⟨.covers 312,1,1⟩,⟨.covers 568,1,2⟩,⟨.covers 344,1,3⟩,⟨.covers 2216,1,1⟩,⟨.covers 2248,1,2⟩,⟨.covers 2824,1,2⟩,⟨.covers 3336,1,5⟩,⟨.covers 1328,1,5⟩,⟨.covers 2608,1,4⟩,⟨.covers 848,1,1⟩,⟨.covers 2832,1,5⟩,⟨.covers 3344,1,4⟩,⟨.covers 2272,1,4⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,11⟩,⟨.covers 2944,1,4⟩,⟨.covers 3456,1,4⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_016
namespace C13.Global.FastDual64_017
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,5,7,9]
def points : Finset C13.Point := {0,5,7,9}
def columns : List Code := [239,638,719,731,830,878,892,967,971,979,1199,1374,1447,1453,1461,1509,1598,1646,1654,1679,1691,1693,1753,1838,1852,1894,1908,1931,1945,1987,2001,2159,2171,2270,2398,2411,2413,2425,2462,2510,2518,2622,2639,2647,2653,2670,2734,2746,2794,2862,2876,2887,2901,2986,3011,3119,3127,3131,3166,3187,3230,3278,3292,3358,3367,3371,3373,3379,3381,3385,3406,3414,3418,3420,3427,3429,3433,3441,3470,3478,3484,3493,3526,3532,3540,3599,3613,3630,3669,3686,3737,3754]
def rows : List LinearRow := [⟨.covers 147,1,2⟩,⟨.covers 149,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 777,1,2⟩,⟨.covers 177,1,1⟩,⟨.covers 166,1,1⟩,⟨.covers 390,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 2704,1,2⟩,⟨.covers 1248,1,2⟩,⟨.covers 928,1,2⟩,⟨.covers 1696,1,2⟩,⟨.covers 1728,1,2⟩,⟨.covers 2752,1,2⟩,⟨.covers 3456,1,1⟩,⟨.incident 7,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_017
namespace C13.Global.FastDual64_018
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,5,7,10]
def points : Finset C13.Point := {0,5,7,10}
def columns : List Code := [239,638,719,731,830,862,878,892,967,971,979,1199,1374,1447,1453,1461,1509,1630,1646,1654,1679,1691,1693,1753,1870,1882,1894,1933,1945,1957,2159,2171,2270,2398,2411,2413,2425,2462,2510,2518,2622,2639,2647,2651,2653,2654,2670,2682,2718,2734,2746,2766,2778,2794,2846,2862,2874,2876,2887,2891,2893,2894,2899,2901,2902,2905,2906,2908,2921,2922,2924,2936,2958,2966,2970,2986,3011,3014,3018,3026,3119,3127,3131,3166,3187,3278,3292,3367,3379,3406,3418,3493,3532,3599,3611,3635,3662,3674,3686,3698,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 135,1,3⟩,⟨.covers 519,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 1043,1,3⟩,⟨.covers 99,1,5⟩,⟨.covers 323,1,1⟩,⟨.covers 1283,1,16⟩,⟨.covers 45,1,9⟩,⟨.covers 1037,1,1⟩,⟨.covers 2061,1,3⟩,⟨.covers 53,1,3⟩,⟨.covers 2069,1,2⟩,⟨.covers 57,1,5⟩,⟨.covers 169,1,1⟩,⟨.covers 329,1,3⟩,⟨.covers 1161,1,1⟩,⟨.covers 1289,1,6⟩,⟨.covers 113,1,8⟩,⟨.covers 177,1,18⟩,⟨.covers 209,1,6⟩,⟨.covers 54,1,11⟩,⟨.covers 774,1,1⟩,⟨.covers 1286,1,3⟩,⟨.covers 1050,1,3⟩,⟨.covers 778,1,1⟩,⟨.covers 156,1,5⟩,⟨.covers 300,1,3⟩,⟨.covers 116,1,8⟩,⟨.covers 212,1,3⟩,⟨.covers 2324,1,3⟩,⟨.covers 184,1,21⟩,⟨.covers 312,1,3⟩,⟨.covers 3336,1,3⟩,⟨.covers 1808,1,1⟩,⟨.covers 736,1,21⟩,⟨.covers 1248,1,21⟩,⟨.covers 864,1,5⟩,⟨.covers 3168,1,3⟩,⟨.covers 2464,1,5⟩,⟨.covers 1696,1,21⟩,⟨.covers 3232,1,13⟩,⟨.covers 2848,1,11⟩,⟨.covers 3616,1,16⟩,⟨.covers 2496,1,3⟩,⟨.covers 1728,1,1⟩,⟨.covers 2944,1,4⟩,⟨.covers 3456,1,3⟩,⟨.covers 3712,1,7⟩,⟨.incident 5,8,-13⟩,⟨.incident 7,8,-3⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_018
namespace C13.Global.FastDual64_019
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,5,7,11]
def points : Finset C13.Point := {0,5,7,11}
def columns : List Code := [239,638,719,731,830,862,878,892,967,971,979,1199,1374,1447,1453,1461,1509,1598,1630,1646,1654,1679,1691,1693,1753,1822,1838,1846,1852,1870,1878,1882,1884,1894,1900,1908,1927,1931,1933,1939,1941,1945,1957,1987,1989,1993,2001,2159,2171,2270,2411,2413,2425,2462,2510,2518,2639,2647,2653,2718,2734,2746,2766,2794,2893,2901,2921,2958,2966,2986,3119,3127,3131,3187,3230,3278,3292,3371,3379,3433,3441,3470,3478,3532,3540,3599,3607,3635,3669,3726,3754,3788,3853,3861,3881,3889,3980,3988,4008,4016]
def rows : List LinearRow := [⟨.covers 163,1,33⟩,⟨.covers 2307,1,33⟩,⟨.covers 53,1,17⟩,⟨.covers 57,1,33⟩,⟨.covers 177,1,17⟩,⟨.covers 54,1,17⟩,⟨.covers 1570,1,17⟩,⟨.covers 300,1,17⟩,⟨.covers 184,1,33⟩,⟨.covers 736,1,17⟩,⟨.covers 1248,1,33⟩,⟨.covers 864,1,17⟩,⟨.covers 2656,1,17⟩,⟨.covers 3168,1,33⟩,⟨.covers 2464,1,17⟩,⟨.covers 3616,1,17⟩,⟨.incident 5,8,-33⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_019
namespace C13.Global.FastDual64_020
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,5,9,10]
def points : Finset C13.Point := {0,5,9,10}
def columns : List Code := [239,253,478,493,638,702,719,727,731,733,750,764,830,878,892,942,956,967,971,979,981,985,1199,1207,1246,1269,1374,1447,1453,1461,1486,1498,1500,1509,1646,1654,1679,1691,1693,1753,1766,1780,1894,1945,2159,2171,2270,2297,2398,2411,2413,2425,2462,2510,2518,2522,2524,2537,2622,2639,2647,2653,2670,2734,2746,2771,2773,2777,2794,2808,2862,2876,2887,2901,2986,3000,3011,3025,3119,3127,3131,3166,3187,3251,3278,3290,3292,3313,3367,3379,3406,3418,3493,3505,3532,3544,3599,3686,3737,3824]
def rows : List LinearRow := [⟨.covers 71,1,19⟩,⟨.covers 43,1,6⟩,⟨.covers 139,1,21⟩,⟨.covers 83,1,24⟩,⟨.covers 147,1,10⟩,⟨.covers 99,1,6⟩,⟨.covers 163,1,5⟩,⟨.covers 387,1,12⟩,⟨.covers 1283,1,17⟩,⟨.covers 77,1,8⟩,⟨.covers 525,1,7⟩,⟨.covers 2061,1,3⟩,⟨.covers 53,1,7⟩,⟨.covers 533,1,2⟩,⟨.covers 2069,1,8⟩,⟨.covers 773,1,15⟩,⟨.covers 1541,1,4⟩,⟨.covers 57,1,12⟩,⟨.covers 297,1,19⟩,⟨.covers 329,1,8⟩,⟨.covers 2577,1,7⟩,⟨.covers 3089,1,4⟩,⟨.covers 353,1,11⟩,⟨.covers 449,1,9⟩,⟨.covers 1793,1,31⟩,⟨.covers 2817,1,2⟩,⟨.covers 3585,1,18⟩,⟨.covers 54,1,12⟩,⟨.covers 2070,1,3⟩,⟨.covers 2182,1,45⟩,⟨.covers 58,1,12⟩,⟨.covers 1098,1,31⟩,⟨.covers 778,1,4⟩,⟨.covers 2194,1,14⟩,⟨.covers 2594,1,17⟩,⟨.covers 706,1,7⟩,⟨.covers 540,1,19⟩,⟨.covers 1292,1,14⟩,⟨.covers 116,1,19⟩,⟨.covers 308,1,14⟩,⟨.covers 2196,1,45⟩,⟨.covers 1796,1,31⟩,⟨.covers 2820,1,27⟩,⟨.covers 3332,1,17⟩,⟨.covers 184,1,19⟩,⟨.covers 1112,1,31⟩,⟨.covers 360,1,9⟩,⟨.covers 2152,1,6⟩,⟨.covers 3336,1,14⟩,⟨.covers 1328,1,13⟩,⟨.covers 2832,1,2⟩,⟨.covers 3600,1,2⟩,⟨.covers 736,1,5⟩,⟨.covers 2272,1,3⟩,⟨.covers 2656,1,14⟩,⟨.covers 928,1,9⟩,⟨.covers 1696,1,7⟩,⟨.covers 1472,1,14⟩,⟨.covers 2944,1,32⟩,⟨.covers 3456,1,17⟩,⟨.incident 0,8,21⟩,⟨.incident 5,8,21⟩,⟨.incident 9,8,24⟩,⟨.incident 10,8,31⟩]
def bound : Int := 108

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_020
namespace C13.Global.FastDual64_021
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,7,9,10]
def points : Finset C13.Point := {0,7,9,10}
def columns : List Code := [239,382,487,638,719,731,830,878,886,892,967,971,979,995,1150,1199,1213,1374,1390,1398,1402,1447,1453,1461,1509,1646,1654,1679,1691,1693,1721,1753,1894,1945,2159,2167,2171,2173,2174,2238,2270,2286,2366,2398,2407,2411,2413,2414,2419,2421,2422,2425,2426,2428,2462,2478,2486,2510,2518,2534,2622,2639,2647,2653,2670,2677,2678,2684,2734,2746,2794,2862,2876,2887,2901,2918,2932,2986,3011,3042,3119,3127,3131,3166,3182,3187,3190,3194,3278,3292,3308,3367,3379,3406,3418,3430,3442,3493,3532,3556,3599,3686,3737]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 1283,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 773,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 1793,1,2⟩,⟨.covers 2817,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 1796,1,2⟩,⟨.covers 624,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 2224,1,1⟩,⟨.covers 3600,1,2⟩,⟨.covers 736,1,1⟩,⟨.covers 1248,1,1⟩,⟨.covers 1696,1,2⟩,⟨.covers 3232,1,1⟩,⟨.covers 3616,1,2⟩,⟨.covers 1728,1,2⟩,⟨.covers 2752,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_021
namespace C13.Global.FastDual64_022
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,5,9]
def points : Finset C13.Point := {2,3,5,9}
def columns : List Code := [253,764,829,830,892,956,979,1243,1255,1269,1371,1447,1461,1491,1497,1498,1509,1639,1654,1691,1747,1753,1766,1780,1852,1894,1908,1945,1987,2001,2263,2283,2297,2411,2425,2455,2515,2517,2518,2537,2647,2731,2746,2771,2773,2794,2808,2876,2901,2986,3000,3011,3025,3187,3251,3271,3275,3277,3278,3283,3285,3286,3289,3290,3292,3299,3313,3379,3403,3411,3417,3418,3427,3433,3441,3463,3475,3477,3478,3491,3493,3505,3523,3525,3526,3529,3530,3532,3537,3538,3540,3544,3553,3655,3669,3686,3723,3737,3754,3779,3793,3810,3824]
def rows : List LinearRow := [⟨.covers 39,1,13⟩,⟨.covers 523,1,1⟩,⟨.covers 83,1,1⟩,⟨.covers 147,1,2⟩,⟨.covers 525,1,19⟩,⟨.covers 1037,1,19⟩,⟨.covers 2309,1,5⟩,⟨.covers 1541,1,1⟩,⟨.covers 1289,1,5⟩,⟨.covers 2569,1,13⟩,⟨.covers 113,1,5⟩,⟨.covers 177,1,3⟩,⟨.covers 1793,1,8⟩,⟨.covers 2817,1,8⟩,⟨.covers 46,1,18⟩,⟨.covers 78,1,19⟩,⟨.covers 54,1,1⟩,⟨.covers 86,1,11⟩,⟨.covers 166,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 154,1,11⟩,⟨.covers 106,1,13⟩,⟨.covers 2098,1,3⟩,⟨.covers 1298,1,3⟩,⟨.covers 2322,1,3⟩,⟨.covers 1570,1,1⟩,⟨.covers 156,1,6⟩,⟨.covers 1292,1,3⟩,⟨.covers 1548,1,17⟩,⟨.covers 2572,1,19⟩,⟨.covers 596,1,1⟩,⟨.covers 3332,1,9⟩,⟨.covers 3588,1,12⟩,⟨.covers 120,1,5⟩,⟨.covers 3336,1,8⟩,⟨.covers 3600,1,1⟩,⟨.covers 864,1,13⟩,⟨.covers 928,1,13⟩,⟨.covers 1696,1,7⟩,⟨.incident 2,8,-6⟩,⟨.incident 3,8,-5⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_022
namespace C13.Global.FastDual64_023
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,5,10]
def points : Finset C13.Point := {2,3,5,10}
def columns : List Code := [253,764,829,830,892,956,979,1243,1255,1269,1371,1447,1461,1497,1498,1509,1639,1654,1691,1753,1754,1766,1780,1819,1831,1882,1894,1945,1957,2008,2020,2263,2283,2297,2411,2425,2455,2515,2517,2518,2537,2647,2731,2746,2771,2773,2774,2794,2808,2839,2859,2873,2874,2876,2899,2901,2902,2921,2922,2936,2963,2965,2966,2985,2986,3000,3011,3025,3026,3028,3048,3187,3251,3277,3278,3289,3290,3292,3313,3379,3418,3493,3505,3532,3544,3635,3686,3698,3737,3788,3800,3824]
def rows : List LinearRow := [⟨.covers 2055,1,6⟩,⟨.covers 525,1,25⟩,⟨.covers 1037,1,25⟩,⟨.covers 2309,1,6⟩,⟨.covers 1541,1,25⟩,⟨.covers 46,1,6⟩,⟨.covers 78,1,25⟩,⟨.covers 54,1,19⟩,⟨.covers 86,1,6⟩,⟨.covers 166,1,25⟩,⟨.covers 2566,1,6⟩,⟨.covers 108,1,6⟩,⟨.covers 172,1,19⟩,⟨.covers 2316,1,6⟩,⟨.covers 2572,1,6⟩,⟨.covers 2132,1,6⟩,⟨.covers 404,1,6⟩,⟨.covers 2196,1,6⟩,⟨.covers 2820,1,6⟩,⟨.covers 3332,1,19⟩,⟨.covers 3588,1,19⟩,⟨.covers 1376,1,25⟩,⟨.incident 2,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_023
