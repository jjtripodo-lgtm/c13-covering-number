import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source60
namespace C13.Global.FastDual60_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,5,6,11]
def points : Finset C13.Point := {1,5,6,11}
def columns : List Code := [445,475,829,925,941,956,967,971,979,1341,1371,1374,1437,1453,1461,1498,1639,1646,1654,1693,1766,1821,1837,1845,1852,1863,1867,1870,1875,1878,1882,1894,1933,1941,1945,1948,1957,1964,1972,1987,1990,1994,2002,2235,2269,2397,2413,2425,2455,2462,2509,2537,2653,2731,2734,2746,2765,2773,2893,2901,2921,2958,2966,2986,3127,3131,3165,3251,3277,3292,3351,3379,3405,3433,3478,3532,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 39,1,8⟩,⟨.covers 135,1,2⟩,⟨.covers 139,1,2⟩,⟨.covers 1035,1,2⟩,⟨.covers 83,1,1⟩,⟨.covers 99,1,10⟩,⟨.covers 163,1,11⟩,⟨.covers 643,1,1⟩,⟨.covers 1283,1,1⟩,⟨.covers 45,1,5⟩,⟨.covers 53,1,5⟩,⟨.covers 197,1,2⟩,⟨.covers 1157,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 2577,1,1⟩,⟨.covers 1185,1,2⟩,⟨.covers 1409,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 166,1,10⟩,⟨.covers 1050,1,1⟩,⟨.covers 106,1,4⟩,⟨.covers 202,1,2⟩,⟨.covers 2314,1,2⟩,⟨.covers 3082,1,11⟩,⟨.covers 114,1,18⟩,⟨.covers 226,1,8⟩,⟨.covers 3586,1,1⟩,⟨.covers 92,1,4⟩,⟨.covers 540,1,1⟩,⟨.covers 108,1,13⟩,⟨.covers 172,1,5⟩,⟨.covers 120,1,17⟩,⟨.covers 568,1,2⟩,⟨.covers 792,1,1⟩,⟨.covers 232,1,18⟩,⟨.covers 3208,1,1⟩,⟨.covers 1328,1,5⟩,⟨.covers 2608,1,12⟩,⟨.covers 848,1,4⟩,⟨.covers 2384,1,1⟩,⟨.covers 3152,1,1⟩,⟨.covers 864,1,11⟩,⟨.covers 1376,1,2⟩,⟨.covers 3168,1,7⟩,⟨.covers 928,1,5⟩,⟨.covers 3232,1,1⟩,⟨.covers 1824,1,5⟩,⟨.covers 2848,1,7⟩,⟨.covers 3360,1,8⟩,⟨.covers 1472,1,2⟩,⟨.covers 2752,1,2⟩,⟨.covers 3648,1,2⟩,⟨.covers 3456,1,2⟩,⟨.incident 5,8,-12⟩,⟨.incident 6,8,-4⟩]
def bound : Int := 3

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_008
namespace C13.Global.FastDual60_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,5,7,10]
def points : Finset C13.Point := {1,5,7,10}
def columns : List Code := [381,471,829,861,877,892,967,971,979,1143,1245,1371,1374,1437,1453,1461,1485,1509,1639,1646,1654,1693,1741,1753,1870,1882,1894,1933,1945,1957,2365,2397,2413,2425,2455,2462,2518,2653,2731,2734,2746,2794,2845,2861,2873,2876,2893,2901,2905,2908,2921,2924,2936,2951,2955,2958,2963,2966,2970,2986,3011,3014,3018,3026,3127,3131,3187,3229,3277,3292,3355,3379,3418,3469,3493,3532,3623,3635,3686,3698,3725,3737,3788,3800,3851,3875,3914,3938,3977,4001,4040,4064]
def rows : List LinearRow := [⟨.covers 43,1,8⟩,⟨.covers 99,1,25⟩,⟨.covers 45,1,8⟩,⟨.covers 169,1,17⟩,⟨.covers 166,1,25⟩,⟨.covers 3078,1,25⟩,⟨.covers 58,1,17⟩,⟨.covers 178,1,8⟩,⟨.covers 226,1,25⟩,⟨.covers 108,1,8⟩,⟨.covers 180,1,25⟩,⟨.covers 228,1,25⟩,⟨.covers 804,1,8⟩,⟨.covers 120,1,8⟩,⟨.covers 2344,1,8⟩,⟨.covers 2352,1,8⟩,⟨.covers 1584,1,25⟩,⟨.covers 928,1,17⟩,⟨.covers 3360,1,8⟩,⟨.incident 5,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_009
namespace C13.Global.FastDual60_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,5,7,11]
def points : Finset C13.Point := {1,5,7,11}
def columns : List Code := [381,471,829,861,877,892,967,971,979,1143,1245,1341,1367,1371,1373,1374,1389,1397,1437,1453,1461,1485,1493,1509,1629,1639,1646,1654,1693,1741,1753,1821,1837,1845,1852,1863,1867,1869,1870,1875,1877,1878,1881,1882,1884,1893,1894,1900,1908,1933,1941,1945,1957,1987,1989,1993,2001,2397,2413,2425,2455,2462,2518,2653,2731,2734,2746,2794,2893,2901,2921,2958,2966,2986,3127,3131,3165,3187,3277,3292,3351,3379,3405,3413,3433,3441,3478,3532,3540,3627,3635,3661,3669,3754,3788]
def rows : List LinearRow := [⟨.covers 135,1,3⟩,⟨.covers 519,1,8⟩,⟨.covers 2055,1,8⟩,⟨.covers 75,1,8⟩,⟨.covers 99,1,3⟩,⟨.covers 163,1,11⟩,⟨.covers 45,1,6⟩,⟨.covers 141,1,6⟩,⟨.covers 2061,1,3⟩,⟨.covers 537,1,3⟩,⟨.covers 201,1,3⟩,⟨.covers 2577,1,3⟩,⟨.covers 2817,1,8⟩,⟨.covers 3585,1,6⟩,⟨.covers 78,1,8⟩,⟨.covers 142,1,6⟩,⟨.covers 54,1,3⟩,⟨.covers 2566,1,6⟩,⟨.covers 58,1,8⟩,⟨.covers 1050,1,3⟩,⟨.covers 114,1,6⟩,⟨.covers 210,1,8⟩,⟨.covers 226,1,11⟩,⟨.covers 1794,1,3⟩,⟨.covers 3330,1,3⟩,⟨.covers 540,1,3⟩,⟨.covers 108,1,3⟩,⟨.covers 180,1,11⟩,⟨.covers 228,1,11⟩,⟨.covers 120,1,3⟩,⟨.covers 216,1,3⟩,⟨.covers 3336,1,8⟩,⟨.covers 2352,1,8⟩,⟨.covers 1584,1,3⟩,⟨.covers 912,1,3⟩,⟨.covers 2704,1,3⟩,⟨.covers 3216,1,8⟩,⟨.covers 864,1,3⟩,⟨.covers 3168,1,3⟩,⟨.covers 2464,1,11⟩,⟨.covers 3232,1,6⟩,⟨.covers 1824,1,6⟩,⟨.covers 2496,1,3⟩,⟨.covers 1728,1,3⟩,⟨.covers 3648,1,3⟩,⟨.covers 1920,1,6⟩,⟨.covers 3712,1,6⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_010
namespace C13.Global.FastDual60_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,5,10,11]
def points : Finset C13.Point := {1,5,10,11}
def columns : List Code := [254,381,445,471,475,477,478,493,508,733,750,829,861,877,892,925,941,956,967,971,973,974,979,981,982,985,986,988,1004,1143,1245,1270,1371,1374,1437,1453,1461,1485,1497,1498,1500,1509,1524,1639,1646,1654,1693,1741,1753,1756,1766,1870,1882,1894,1933,1945,1957,1996,2008,2020,2235,2269,2298,2397,2413,2425,2455,2462,2509,2517,2518,2524,2537,2552,2653,2731,2734,2746,2765,2773,2780,2794,2893,2901,2921,2958,2966,2986,3020,3028,3048,3127,3131,3187,3251,3277,3292,3314,3379,3532,3568,3635,3788]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 1037,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 1289,1,1⟩,⟨.covers 3329,1,2⟩,⟨.covers 3585,1,2⟩,⟨.covers 1038,1,1⟩,⟨.covers 2062,1,1⟩,⟨.covers 3078,1,2⟩,⟨.covers 3082,1,2⟩,⟨.covers 226,1,1⟩,⟨.covers 3336,1,2⟩,⟨.covers 3592,1,2⟩,⟨.covers 368,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 1824,1,1⟩,⟨.covers 2848,1,1⟩,⟨.incident 10,8,-1⟩,⟨.incident 11,8,-1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_011
namespace C13.Global.FastDual60_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,10]
def points : Finset C13.Point := {1,6,7,10}
def columns : List Code := [829,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1639,1646,1654,1693,1709,1721,1870,1882,1894,1906,1933,1945,1957,1969,2173,2238,2365,2397,2413,2425,2455,2462,2486,2621,2653,2669,2677,2731,2734,2746,2845,2861,2869,2873,2876,2893,2901,2905,2917,2921,2929,2951,2955,2958,2963,2966,2970,2979,2982,2986,2994,3011,3127,3131,3229,3245,3277,3292,3308,3355,3379,3418,3469,3493,3532,3623,3635,3686,3725,3737,3788,3851,3875,3914,3938,3977,4001,4040,4064]
def rows : List LinearRow := [⟨.covers 75,1,19⟩,⟨.covers 99,1,19⟩,⟨.covers 77,1,6⟩,⟨.covers 101,1,6⟩,⟨.covers 197,1,19⟩,⟨.covers 89,1,6⟩,⟨.covers 2369,1,6⟩,⟨.covers 2625,1,6⟩,⟨.covers 198,1,6⟩,⟨.covers 1286,1,25⟩,⟨.covers 106,1,25⟩,⟨.covers 202,1,6⟩,⟨.covers 210,1,25⟩,⟨.covers 226,1,6⟩,⟨.covers 212,1,19⟩,⟨.covers 228,1,25⟩,⟨.covers 2628,1,6⟩,⟨.covers 2160,1,6⟩,⟨.covers 2384,1,6⟩,⟨.covers 1616,1,25⟩,⟨.covers 3152,1,6⟩,⟨.covers 2496,1,12⟩,⟨.covers 3392,1,12⟩,⟨.incident 6,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_012
namespace C13.Global.FastDual60_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,7,11]
def points : Finset C13.Point := {1,6,7,11}
def columns : List Code := [829,967,971,979,995,1150,1213,1341,1371,1374,1402,1437,1453,1461,1597,1639,1646,1654,1693,1709,1721,1821,1837,1845,1849,1852,1863,1867,1870,1875,1878,1882,1891,1894,1898,1906,1933,1941,1945,1957,1961,1969,1987,2173,2238,2397,2413,2425,2455,2462,2486,2653,2669,2677,2731,2734,2746,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3165,3181,3277,3292,3308,3351,3379,3405,3433,3478,3532,3627,3635,3661,3669,3754,3788]
def rows : List LinearRow := [⟨.covers 147,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 198,1,2⟩,⟨.covers 2566,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 202,1,2⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 2464,1,1⟩,⟨.covers 2496,1,2⟩,⟨.covers 1728,1,1⟩,⟨.incident 6,8,-1⟩,⟨.incident 7,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_013
namespace C13.Global.FastDual60_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,10,11]
def points : Finset C13.Point := {1,6,10,11}
def columns : List Code := [445,475,701,743,829,925,941,949,953,956,967,971,979,995,1150,1213,1371,1374,1402,1437,1453,1461,1465,1498,1639,1646,1654,1693,1709,1717,1721,1766,1870,1882,1894,1906,1933,1945,1957,1969,2173,2231,2235,2238,2269,2285,2397,2413,2425,2455,2462,2483,2486,2490,2509,2537,2653,2669,2677,2731,2734,2739,2742,2746,2765,2773,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3251,3277,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 135,1,1⟩,⟨.covers 523,1,4⟩,⟨.covers 1283,1,9⟩,⟨.covers 1539,1,8⟩,⟨.covers 1037,1,5⟩,⟨.covers 197,1,1⟩,⟨.covers 2309,1,5⟩,⟨.covers 1541,1,5⟩,⟨.covers 3077,1,11⟩,⟨.covers 537,1,4⟩,⟨.covers 1289,1,5⟩,⟨.covers 2569,1,2⟩,⟨.covers 3329,1,7⟩,⟨.covers 3585,1,9⟩,⟨.covers 46,1,1⟩,⟨.covers 142,1,3⟩,⟨.covers 86,1,11⟩,⟨.covers 1286,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 3078,1,6⟩,⟨.covers 2314,1,3⟩,⟨.covers 1546,1,12⟩,⟨.covers 3082,1,17⟩,⟨.covers 178,1,1⟩,⟨.covers 210,1,4⟩,⟨.covers 596,1,1⟩,⟨.covers 420,1,4⟩,⟨.covers 1316,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 1560,1,1⟩,⟨.covers 2344,1,2⟩,⟨.covers 2600,1,1⟩,⟨.covers 3336,1,11⟩,⟨.covers 3592,1,13⟩,⟨.covers 368,1,1⟩,⟨.covers 2160,1,3⟩,⟨.covers 1200,1,5⟩,⟨.covers 1616,1,1⟩,⟨.covers 3152,1,17⟩,⟨.covers 1424,1,5⟩,⟨.covers 2704,1,4⟩,⟨.covers 480,1,4⟩,⟨.covers 1248,1,6⟩,⟨.covers 1376,1,12⟩,⟨.covers 2656,1,2⟩,⟨.covers 2464,1,1⟩,⟨.covers 1696,1,5⟩,⟨.covers 3232,1,11⟩,⟨.covers 1472,1,5⟩,⟨.covers 1728,1,3⟩,⟨.incident 10,8,-10⟩,⟨.incident 11,8,-3⟩]
def bound : Int := 5

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_014
namespace C13.Global.FastDual60_015
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,7,10,11]
def points : Finset C13.Point := {1,7,10,11}
def columns : List Code := [381,471,637,747,829,861,877,885,889,892,967,971,979,995,1143,1147,1150,1213,1245,1261,1371,1374,1395,1398,1402,1437,1453,1461,1485,1509,1639,1646,1651,1654,1658,1693,1709,1721,1741,1753,1870,1882,1894,1906,1933,1945,1957,1969,2173,2238,2397,2413,2421,2425,2455,2462,2486,2518,2653,2669,2677,2681,2731,2734,2746,2794,2893,2901,2921,2929,2958,2966,2986,2994,3127,3131,3187,3277,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 519,1,4⟩,⟨.covers 1283,1,2⟩,⟨.covers 2307,1,8⟩,⟨.covers 2563,1,8⟩,⟨.covers 141,1,1⟩,⟨.covers 2061,1,4⟩,⟨.covers 533,1,4⟩,⟨.covers 2309,1,4⟩,⟨.covers 1541,1,2⟩,⟨.covers 3077,1,11⟩,⟨.covers 1289,1,5⟩,⟨.covers 2569,1,4⟩,⟨.covers 3329,1,6⟩,⟨.covers 3585,1,8⟩,⟨.covers 78,1,5⟩,⟨.covers 166,1,12⟩,⟨.covers 1286,1,2⟩,⟨.covers 3078,1,5⟩,⟨.covers 202,1,4⟩,⟨.covers 2314,1,12⟩,⟨.covers 1546,1,1⟩,⟨.covers 3082,1,16⟩,⟨.covers 114,1,1⟩,⟨.covers 210,1,4⟩,⟨.covers 1316,1,2⟩,⟨.covers 1572,1,2⟩,⟨.covers 1304,1,1⟩,⟨.covers 1560,1,1⟩,⟨.covers 360,1,4⟩,⟨.covers 3336,1,12⟩,⟨.covers 3592,1,10⟩,⟨.covers 2160,1,4⟩,⟨.covers 1200,1,5⟩,⟨.covers 2384,1,4⟩,⟨.covers 1616,1,5⟩,⟨.covers 3152,1,11⟩,⟨.covers 1424,1,1⟩,⟨.covers 2704,1,12⟩,⟨.covers 3216,1,5⟩,⟨.covers 480,1,4⟩,⟨.covers 1376,1,2⟩,⟨.covers 2656,1,4⟩,⟨.covers 1696,1,2⟩,⟨.covers 3232,1,16⟩,⟨.covers 2496,1,4⟩,⟨.covers 1728,1,2⟩,⟨.covers 2752,1,4⟩,⟨.incident 10,8,-4⟩,⟨.incident 11,8,-8⟩]
def bound : Int := 4

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_015
