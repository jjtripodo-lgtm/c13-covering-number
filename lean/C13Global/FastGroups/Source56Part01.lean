import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source56
namespace C13.Global.FastDual56_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,11]
def points : Finset C13.Point := {1,3,7,11}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1651,1653,1654,1693,1721,1753,1821,1845,1849,1852,1863,1875,1877,1878,1881,1882,1884,1891,1893,1894,1905,1906,1908,1912,1941,1945,1957,1969,1987,1989,2001,2017,2413,2421,2425,2455,2486,2518,2677,2731,2734,2746,2794,2901,2921,2929,2966,2986,2994,3127,3187,3189,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 519,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 2256,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source56.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source56.rootCodes link56 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual56_008
namespace C13.Global.FastDual56_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,5,7,10]
def points : Finset C13.Point := {1,5,7,10}
def columns : List Code := [381,471,829,861,877,892,967,971,979,1143,1245,1371,1374,1437,1453,1461,1485,1509,1639,1646,1654,1693,1741,1753,1870,1882,1894,1933,1945,1957,2365,2397,2413,2425,2455,2462,2518,2653,2731,2734,2746,2794,2845,2861,2873,2876,2893,2901,2905,2908,2921,2924,2936,2951,2955,2958,2963,2966,2970,2986,3011,3014,3018,3026,3127,3131,3187,3229,3277,3292,3355,3379,3418,3469,3493,3532,3623,3635,3686,3698,3725,3737,3788,3800,3854,3866,3878,3890,3980,3992,4004,4016]
def rows : List LinearRow := [⟨.covers 163,1,1⟩,⟨.covers 1539,1,2⟩,⟨.covers 45,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 2337,1,1⟩,⟨.covers 46,1,2⟩,⟨.covers 54,1,2⟩,⟨.covers 58,1,2⟩,⟨.covers 226,1,2⟩,⟨.covers 180,1,2⟩,⟨.covers 228,1,2⟩,⟨.covers 120,1,1⟩,⟨.covers 864,1,1⟩,⟨.covers 3168,1,2⟩,⟨.covers 928,1,1⟩,⟨.covers 3360,1,1⟩,⟨.incident 5,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source56.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source56.rootCodes link56 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual56_009
namespace C13.Global.FastDual56_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,5,7,11]
def points : Finset C13.Point := {1,5,7,11}
def columns : List Code := [381,471,829,861,877,892,967,971,979,1143,1245,1341,1367,1371,1373,1374,1389,1397,1437,1453,1461,1485,1493,1509,1629,1639,1646,1654,1693,1741,1753,1821,1837,1845,1852,1863,1867,1869,1870,1875,1877,1878,1881,1882,1884,1893,1894,1900,1908,1933,1941,1945,1957,1987,1989,1993,2001,2397,2413,2425,2455,2462,2518,2653,2731,2734,2746,2794,2893,2901,2921,2958,2966,2986,3127,3131,3165,3187,3277,3292,3351,3379,3405,3413,3433,3441,3478,3532,3540,3627,3635,3661,3669,3754,3788]
def rows : List LinearRow := [⟨.covers 519,1,11⟩,⟨.covers 75,1,3⟩,⟨.covers 1035,1,8⟩,⟨.covers 163,1,8⟩,⟨.covers 2307,1,11⟩,⟨.covers 45,1,4⟩,⟨.covers 141,1,4⟩,⟨.covers 525,1,1⟩,⟨.covers 2061,1,6⟩,⟨.covers 57,1,3⟩,⟨.covers 2569,1,3⟩,⟨.covers 78,1,11⟩,⟨.covers 54,1,11⟩,⟨.covers 166,1,11⟩,⟨.covers 154,1,8⟩,⟨.covers 202,1,8⟩,⟨.covers 178,1,3⟩,⟨.covers 210,1,11⟩,⟨.covers 156,1,3⟩,⟨.covers 180,1,11⟩,⟨.covers 228,1,11⟩,⟨.covers 120,1,4⟩,⟨.covers 216,1,4⟩,⟨.covers 792,1,2⟩,⟨.covers 1560,1,2⟩,⟨.covers 3336,1,4⟩,⟨.covers 2160,1,4⟩,⟨.covers 3216,1,4⟩,⟨.covers 1808,1,1⟩,⟨.covers 2832,1,11⟩,⟨.covers 3600,1,11⟩,⟨.covers 864,1,5⟩,⟨.covers 2656,1,3⟩,⟨.covers 3168,1,6⟩,⟨.covers 2464,1,11⟩,⟨.covers 3232,1,11⟩,⟨.covers 1824,1,5⟩,⟨.covers 1728,1,5⟩,⟨.covers 1920,1,5⟩,⟨.covers 3456,1,6⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source56.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source56.rootCodes link56 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual56_010
namespace C13.Global.FastDual56_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,5,10,11]
def points : Finset C13.Point := {1,5,10,11}
def columns : List Code := [254,381,445,471,475,477,478,493,508,733,750,829,861,877,892,925,941,956,967,971,973,974,979,981,982,985,986,988,1004,1143,1245,1270,1371,1374,1437,1453,1461,1485,1497,1498,1500,1509,1524,1639,1646,1654,1693,1741,1753,1756,1766,1870,1882,1894,1933,1945,1957,1996,2008,2020,2235,2269,2298,2397,2413,2425,2455,2462,2509,2517,2518,2524,2537,2552,2653,2731,2734,2746,2765,2773,2780,2794,2893,2901,2921,2958,2966,2986,3020,3028,3048,3127,3131,3187,3251,3277,3292,3314,3379,3532,3568,3635,3788]
def rows : List LinearRow := [⟨.covers 135,1,8⟩,⟨.covers 75,1,10⟩,⟨.covers 99,1,12⟩,⟨.covers 163,1,11⟩,⟨.covers 525,1,2⟩,⟨.covers 1037,1,8⟩,⟨.covers 2061,1,5⟩,⟨.covers 197,1,2⟩,⟨.covers 2309,1,5⟩,⟨.covers 3077,1,2⟩,⟨.covers 537,1,2⟩,⟨.covers 1289,1,5⟩,⟨.covers 2129,1,2⟩,⟨.covers 1169,1,3⟩,⟨.covers 353,1,2⟩,⟨.covers 417,1,3⟩,⟨.covers 1038,1,11⟩,⟨.covers 2062,1,11⟩,⟨.covers 1286,1,4⟩,⟨.covers 3078,1,15⟩,⟨.covers 554,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 3082,1,17⟩,⟨.covers 226,1,6⟩,⟨.covers 610,1,3⟩,⟨.covers 3330,1,17⟩,⟨.covers 3586,1,16⟩,⟨.covers 180,1,4⟩,⟨.covers 564,1,1⟩,⟨.covers 3332,1,17⟩,⟨.covers 3588,1,17⟩,⟨.covers 568,1,4⟩,⟨.covers 368,1,5⟩,⟨.covers 2160,1,3⟩,⟨.covers 432,1,1⟩,⟨.covers 1584,1,1⟩,⟨.covers 1616,1,10⟩,⟨.covers 2704,1,8⟩,⟨.covers 3216,1,4⟩,⟨.covers 1808,1,5⟩,⟨.covers 2832,1,5⟩,⟨.covers 1248,1,3⟩,⟨.covers 2272,1,2⟩,⟨.covers 1696,1,4⟩,⟨.covers 1824,1,9⟩,⟨.covers 2848,1,10⟩,⟨.incident 10,8,-5⟩,⟨.incident 11,8,-2⟩]
def bound : Int := 11

theorem column_mask : listMask columns = restrictMask universeMask Source56.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source56.rootCodes link56 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual56_011
namespace C13.Global.FastDual56_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,10,11]
def points : Finset C13.Point := {1,7,10,11}
def columns : List Code := [381,471,637,747,829,861,877,885,889,892,967,971,979,995,1143,1147,1150,1213,1245,1261,1371,1374,1395,1398,1402,1437,1453,1461,1485,1509,1639,1646,1651,1654,1658,1693,1709,1721,1741,1753,1870,1882,1894,1906,1933,1945,1957,1969,2173,2238,2397,2413,2421,2425,2455,2462,2486,2518,2653,2669,2677,2681,2731,2734,2746,2794,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3187,3277,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 519,1,4⟩,⟨.covers 139,1,1⟩,⟨.covers 1283,1,2⟩,⟨.covers 2307,1,8⟩,⟨.covers 141,1,1⟩,⟨.covers 2061,1,4⟩,⟨.covers 533,1,4⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,2⟩,⟨.covers 1289,1,5⟩,⟨.covers 2569,1,4⟩,⟨.covers 78,1,5⟩,⟨.covers 166,1,12⟩,⟨.covers 1286,1,2⟩,⟨.covers 3078,1,16⟩,⟨.covers 202,1,3⟩,⟨.covers 2314,1,12⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,16⟩,⟨.covers 114,1,1⟩,⟨.covers 210,1,4⟩,⟨.covers 3330,1,6⟩,⟨.covers 3586,1,16⟩,⟨.covers 1316,1,2⟩,⟨.covers 1572,1,2⟩,⟨.covers 3332,1,16⟩,⟨.covers 3588,1,14⟩,⟨.covers 1304,1,1⟩,⟨.covers 1560,1,1⟩,⟨.covers 360,1,4⟩,⟨.covers 2160,1,4⟩,⟨.covers 1200,1,5⟩,⟨.covers 2256,1,4⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,5⟩,⟨.covers 1424,1,1⟩,⟨.covers 2704,1,12⟩,⟨.covers 3216,1,12⟩,⟨.covers 480,1,4⟩,⟨.covers 2272,1,5⟩,⟨.covers 1376,1,2⟩,⟨.covers 2656,1,4⟩,⟨.covers 3168,1,11⟩,⟨.covers 1696,1,2⟩,⟨.covers 1728,1,2⟩,⟨.incident 10,8,-4⟩,⟨.incident 11,8,-8⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source56.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source56.rootCodes link56 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual56_012
namespace C13.Global.FastDual56_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,5,7,10]
def points : Finset C13.Point := {3,5,7,10}
def columns : List Code := [381,471,829,830,855,892,919,967,979,1143,1245,1335,1371,1374,1383,1447,1461,1509,1591,1639,1654,1691,1693,1753,1819,1831,1882,1894,1945,1957,2391,2411,2413,2425,2455,2503,2518,2647,2731,2734,2746,2794,2839,2859,2861,2862,2873,2874,2876,2887,2899,2901,2902,2921,2922,2924,2936,2951,2963,2966,2986,3011,3014,3026,3127,3175,3187,3277,3278,3292,3367,3379,3406,3418,3493,3532,3623,3635,3686,3698,3725,3737,3788,3800,3854,3866,3878,3890,3980,3992,4004,4016]
def rows : List LinearRow := [⟨.covers 135,1,6⟩,⟨.covers 139,1,6⟩,⟨.covers 147,1,6⟩,⟨.covers 163,1,19⟩,⟨.covers 3081,1,25⟩,⟨.covers 897,1,6⟩,⟨.covers 198,1,6⟩,⟨.covers 154,1,12⟩,⟨.covers 202,1,19⟩,⟨.covers 178,1,12⟩,⟨.covers 210,1,6⟩,⟨.covers 226,1,6⟩,⟨.covers 898,1,6⟩,⟨.covers 2434,1,6⟩,⟨.covers 156,1,25⟩,⟨.covers 172,1,25⟩,⟨.covers 180,1,25⟩,⟨.covers 228,1,6⟩,⟨.covers 2464,1,6⟩,⟨.covers 1472,1,19⟩,⟨.covers 2496,1,6⟩,⟨.covers 1728,1,25⟩,⟨.covers 1920,1,19⟩,⟨.incident 7,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source56.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source56.rootCodes link56 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual56_013
namespace C13.Global.FastDual56_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,5,7,11]
def points : Finset C13.Point := {3,5,7,11}
def columns : List Code := [381,471,829,830,855,892,919,967,979,1143,1245,1335,1367,1371,1373,1374,1383,1397,1431,1447,1461,1479,1493,1509,1591,1623,1639,1654,1691,1693,1753,1815,1819,1821,1822,1831,1845,1846,1852,1863,1875,1877,1878,1881,1882,1884,1893,1894,1908,1927,1939,1941,1945,1957,1987,1989,2001,2391,2411,2413,2425,2455,2518,2647,2731,2734,2746,2794,2839,2859,2901,2921,2966,2986,3127,3159,3187,3277,3278,3292,3351,3379,3405,3413,3433,3441,3478,3532,3540,3607,3635,3669,3726,3754,3788]
def rows : List LinearRow := [⟨.covers 39,1,5⟩,⟨.covers 135,1,5⟩,⟨.covers 2055,1,3⟩,⟨.covers 75,1,3⟩,⟨.covers 1035,1,8⟩,⟨.covers 147,1,3⟩,⟨.covers 579,1,3⟩,⟨.covers 525,1,8⟩,⟨.covers 2061,1,3⟩,⟨.covers 57,1,3⟩,⟨.covers 169,1,3⟩,⟨.covers 201,1,8⟩,⟨.covers 2569,1,8⟩,⟨.covers 78,1,3⟩,⟨.covers 1038,1,8⟩,⟨.covers 54,1,3⟩,⟨.covers 582,1,3⟩,⟨.covers 58,1,8⟩,⟨.covers 106,1,8⟩,⟨.covers 114,1,3⟩,⟨.covers 178,1,3⟩,⟨.covers 210,1,3⟩,⟨.covers 226,1,3⟩,⟨.covers 3330,1,8⟩,⟨.covers 156,1,3⟩,⟨.covers 172,1,11⟩,⟨.covers 2316,1,8⟩,⟨.covers 180,1,11⟩,⟨.covers 228,1,11⟩,⟨.covers 2628,1,3⟩,⟨.covers 2820,1,8⟩,⟨.covers 120,1,8⟩,⟨.covers 1800,1,3⟩,⟨.covers 1584,1,3⟩,⟨.covers 2256,1,5⟩,⟨.covers 912,1,3⟩,⟨.covers 3216,1,3⟩,⟨.covers 3600,1,8⟩,⟨.covers 864,1,3⟩,⟨.covers 3168,1,8⟩,⟨.covers 2464,1,11⟩,⟨.covers 3232,1,11⟩,⟨.covers 1824,1,5⟩,⟨.covers 3360,1,3⟩,⟨.covers 2496,1,3⟩,⟨.covers 1728,1,3⟩,⟨.covers 1920,1,5⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source56.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source56.rootCodes link56 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual56_014
