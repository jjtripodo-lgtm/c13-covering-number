import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source51
namespace C13.Global.FastDual51_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,9,11]
def points : Finset C13.Point := {1,3,9,11}
def columns : List Code := [247,251,253,254,381,471,499,501,502,505,506,508,701,743,755,757,758,761,762,764,829,885,892,953,956,967,979,981,995,998,1009,1010,1012,1016,1143,1245,1267,1269,1270,1273,1274,1276,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1491,1493,1494,1497,1498,1500,1509,1521,1522,1524,1528,1639,1653,1654,1693,1721,1724,1749,1753,1763,1766,1777,1778,1780,1784,1821,1852,1863,1877,1894,1908,1945,1976,1987,2001,2018,2032,2231,2285,2291,2293,2294,2297,2298,2300,2413,2421,2425,2455,2483,2486,2517,2518,2537,2540,2545,2546,2548,2552,2677,2731,2734,2746,2773,2794,2801,2802,2804,2808,2901,2986,3056,3127,3187,3189,3251,3254,3277,3285,3292,3305,3308,3313,3314,3316,3320,3351,3379,3405,3413,3433,3441,3478,3506,3532,3540,3560,3568,3669,3754,3824]
def rows : List LinearRow := [⟨.covers 135,1,7⟩,⟨.covers 519,1,3⟩,⟨.covers 2055,1,6⟩,⟨.covers 267,1,19⟩,⟨.covers 523,1,19⟩,⟨.covers 99,1,2⟩,⟨.covers 2307,1,1⟩,⟨.covers 1539,1,11⟩,⟨.covers 141,1,7⟩,⟨.covers 525,1,6⟩,⟨.covers 2061,1,3⟩,⟨.covers 201,1,7⟩,⟨.covers 777,1,7⟩,⟨.covers 3081,1,1⟩,⟨.covers 2097,1,5⟩,⟨.covers 657,1,2⟩,⟨.covers 2145,1,2⟩,⟨.covers 417,1,8⟩,⟨.covers 705,1,1⟩,⟨.covers 2817,1,19⟩,⟨.covers 3585,1,19⟩,⟨.covers 270,1,19⟩,⟨.covers 526,1,19⟩,⟨.covers 198,1,4⟩,⟨.covers 774,1,3⟩,⟨.covers 3078,1,7⟩,⟨.covers 154,1,1⟩,⟨.covers 106,1,9⟩,⟨.covers 778,1,19⟩,⟨.covers 1546,1,19⟩,⟨.covers 1074,1,2⟩,⟨.covers 402,1,3⟩,⟨.covers 2194,1,2⟩,⟨.covers 610,1,1⟩,⟨.covers 1122,1,1⟩,⟨.covers 450,1,1⟩,⟨.covers 706,1,1⟩,⟨.covers 1794,1,3⟩,⟨.covers 3330,1,6⟩,⟨.covers 300,1,1⟩,⟨.covers 2316,1,13⟩,⟨.covers 1548,1,1⟩,⟨.covers 116,1,5⟩,⟨.covers 564,1,3⟩,⟨.covers 612,1,1⟩,⟨.covers 420,1,2⟩,⟨.covers 1188,1,8⟩,⟨.covers 2436,1,1⟩,⟨.covers 568,1,2⟩,⟨.covers 1176,1,5⟩,⟨.covers 2152,1,1⟩,⟨.covers 1224,1,2⟩,⟨.covers 2248,1,1⟩,⟨.covers 1800,1,6⟩,⟨.covers 3336,1,3⟩,⟨.covers 2608,1,4⟩,⟨.covers 464,1,5⟩,⟨.covers 864,1,4⟩,⟨.covers 3168,1,7⟩,⟨.covers 1824,1,7⟩,⟨.covers 3360,1,7⟩,⟨.covers 1728,1,2⟩,⟨.covers 2752,1,6⟩]
def bound : Int := 21

theorem column_mask : listMask columns = restrictMask universeMask Source51.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source51.rootCodes link51 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual51_008
namespace C13.Global.FastDual51_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,6,8,11]
def points : Finset C13.Point := {1,6,8,11}
def columns : List Code := [254,445,475,506,701,743,758,829,941,949,956,967,971,979,995,1010,1150,1213,1341,1371,1374,1402,1453,1461,1468,1498,1597,1639,1646,1654,1693,1709,1717,1721,1724,1766,1837,1852,1867,1882,1957,1972,1987,2002,2173,2231,2235,2238,2269,2285,2300,2413,2425,2455,2462,2486,2537,2552,2653,2669,2677,2731,2734,2739,2742,2746,2765,2773,2804,2921,2966,3056,3127,3131,3165,3181,3251,3254,3258,3277,3292,3308,3433,3478,3627,3635,3661,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 263,1,19⟩,⟨.covers 83,1,25⟩,⟨.covers 2307,1,6⟩,⟨.covers 269,1,6⟩,⟨.covers 773,1,6⟩,⟨.covers 417,1,6⟩,⟨.covers 2817,1,25⟩,⟨.covers 3329,1,25⟩,⟨.covers 270,1,6⟩,⟨.covers 1286,1,12⟩,⟨.covers 778,1,25⟩,⟨.covers 2818,1,25⟩,⟨.covers 3330,1,13⟩,⟨.covers 1292,1,6⟩,⟨.covers 2316,1,19⟩,⟨.covers 308,1,6⟩,⟨.covers 420,1,6⟩,⟨.covers 1796,1,6⟩,⟨.covers 368,1,19⟩,⟨.covers 1328,1,6⟩,⟨.covers 480,1,6⟩,⟨.covers 1472,1,25⟩,⟨.incident 8,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source51.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source51.rootCodes link51 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual51_009
namespace C13.Global.FastDual51_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,8]
def points : Finset C13.Point := {2,3,6,8}
def columns : List Code := [254,379,439,506,631,699,758,829,830,949,950,956,979,995,1010,1371,1402,1447,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1852,1882,1957,1972,1987,2002,2300,2411,2425,2455,2485,2486,2537,2552,2647,2677,2731,2739,2745,2746,2773,2804,2876,2921,2966,2996,3011,3041,3056,3251,3277,3278,3292,3308,3403,3418,3433,3448,3463,3478,3493,3508,3635,3655,3669,3670,3685,3686,3700,3723,3731,3737,3738,3747,3753,3754,3761,3762,3768,3781,3782,3788,3796,3812]
def rows : List LinearRow := [⟨.covers 139,1,6⟩,⟨.covers 77,1,25⟩,⟨.covers 269,1,25⟩,⟨.covers 89,1,25⟩,⟨.covers 169,1,6⟩,⟨.covers 2569,1,6⟩,⟨.covers 270,1,6⟩,⟨.covers 1038,1,25⟩,⟨.covers 778,1,19⟩,⟨.covers 2314,1,25⟩,⟨.covers 1546,1,6⟩,⟨.covers 108,1,25⟩,⟨.covers 1292,1,6⟩,⟨.covers 2316,1,6⟩,⟨.covers 1548,1,19⟩,⟨.covers 664,1,6⟩,⟨.covers 1176,1,6⟩,⟨.covers 680,1,6⟩,⟨.covers 2824,1,19⟩,⟨.covers 3592,1,6⟩,⟨.covers 1376,1,25⟩,⟨.incident 3,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source51.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source51.rootCodes link51 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual51_010
namespace C13.Global.FastDual51_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,3,6,11]
def points : Finset C13.Point := {2,3,6,11}
def columns : List Code := [254,379,439,506,631,699,758,823,827,829,830,883,947,949,950,953,954,956,979,995,1010,1371,1402,1447,1459,1461,1462,1498,1639,1654,1691,1715,1721,1722,1766,1819,1831,1843,1845,1846,1849,1850,1852,1875,1882,1891,1894,1906,1939,1945,1946,1955,1957,1958,1969,1970,1972,1976,1987,2002,2018,2300,2411,2425,2455,2483,2486,2537,2552,2647,2677,2731,2739,2746,2773,2804,2839,2859,2867,2901,2921,2929,2966,2986,2994,3056,3251,3277,3278,3292,3308,3379,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 135,1,4⟩,⟨.covers 1031,1,4⟩,⟨.covers 75,1,2⟩,⟨.covers 139,1,5⟩,⟨.covers 1035,1,2⟩,⟨.covers 77,1,17⟩,⟨.covers 269,1,17⟩,⟨.covers 149,1,10⟩,⟨.covers 101,1,6⟩,⟨.covers 89,1,8⟩,⟨.covers 169,1,9⟩,⟨.covers 2129,1,1⟩,⟨.covers 449,1,3⟩,⟨.covers 705,1,1⟩,⟨.covers 2369,1,1⟩,⟨.covers 1665,1,3⟩,⟨.covers 270,1,17⟩,⟨.covers 1038,1,17⟩,⟨.covers 86,1,1⟩,⟨.covers 1286,1,3⟩,⟨.covers 2566,1,11⟩,⟨.covers 2314,1,10⟩,⟨.covers 1546,1,3⟩,⟨.covers 210,1,1⟩,⟨.covers 1106,1,2⟩,⟨.covers 226,1,3⟩,⟨.covers 1122,1,4⟩,⟨.covers 450,1,4⟩,⟨.covers 3330,1,11⟩,⟨.covers 3586,1,11⟩,⟨.covers 2316,1,17⟩,⟨.covers 2572,1,17⟩,⟨.covers 116,1,6⟩,⟨.covers 1188,1,4⟩,⟨.covers 1796,1,6⟩,⟨.covers 2820,1,3⟩,⟨.covers 120,1,4⟩,⟨.covers 216,1,2⟩,⟨.covers 1176,1,2⟩,⟨.covers 1800,1,9⟩,⟨.covers 2824,1,4⟩,⟨.covers 464,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 3152,1,13⟩,⟨.covers 3168,1,13⟩,⟨.covers 1824,1,1⟩,⟨.covers 2880,1,9⟩,⟨.incident 2,8,-3⟩,⟨.incident 3,8,-3⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source51.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source51.rootCodes link51 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual51_011
