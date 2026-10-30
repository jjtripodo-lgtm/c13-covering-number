import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source64
namespace C13.Global.FastDual64_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,2,7,11]
def points : Finset C13.Point := {0,2,7,11}
def columns : List Code := [638,731,830,886,890,892,971,979,995,1402,1447,1453,1461,1509,1646,1654,1658,1660,1691,1721,1753,1838,1846,1850,1852,1882,1894,1898,1900,1906,1908,1912,1931,1939,1945,1955,1957,1961,1969,1987,1993,2001,2017,2171,2270,2411,2419,2425,2462,2486,2518,2647,2653,2675,2677,2681,2746,2794,2901,2921,2929,2966,2986,2994,3131,3187,3193,3278,3292,3308,3371,3379,3433,3441,3470,3478,3532,3540,3635,3669,3697,3754,3788,3816,3853,3861,3881,3889,3980,3988,4008,4016]
def rows : List LinearRow := [⟨.covers 71,1,2⟩,⟨.covers 77,1,2⟩,⟨.covers 149,1,2⟩,⟨.covers 197,1,2⟩,⟨.covers 773,1,2⟩,⟨.covers 46,1,1⟩,⟨.covers 166,1,2⟩,⟨.covers 774,1,1⟩,⟨.covers 3078,1,2⟩,⟨.covers 156,1,2⟩,⟨.covers 172,1,2⟩,⟨.covers 116,1,1⟩,⟨.covers 1604,1,1⟩,⟨.covers 2496,1,2⟩,⟨.incident 2,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_008
namespace C13.Global.FastDual64_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,2,9,11]
def points : Finset C13.Point := {0,2,9,11}
def columns : List Code := [247,251,253,254,446,491,499,501,502,505,506,508,638,731,755,757,758,761,762,764,830,886,892,954,956,971,979,985,995,1002,1009,1010,1012,1016,1211,1262,1267,1269,1270,1273,1274,1276,1402,1447,1451,1453,1454,1459,1461,1462,1465,1466,1468,1498,1507,1509,1510,1513,1514,1516,1521,1522,1524,1528,1646,1654,1660,1691,1721,1722,1747,1753,1766,1770,1777,1778,1780,1784,1838,1852,1894,1908,1931,1945,1962,1976,1987,2001,2018,2032,2171,2270,2291,2293,2294,2297,2298,2300,2411,2419,2425,2462,2486,2490,2518,2524,2537,2538,2545,2546,2548,2552,2647,2653,2677,2746,2773,2794,2801,2802,2804,2808,2901,2986,3056,3131,3187,3193,3251,3258,3278,3286,3292,3306,3308,3313,3314,3316,3320,3371,3379,3433,3441,3470,3478,3498,3506,3532,3540,3560,3568,3669,3754,3824]
def rows : List LinearRow := [⟨.covers 519,1,19⟩,⟨.covers 1031,1,19⟩,⟨.covers 75,1,8⟩,⟨.covers 523,1,4⟩,⟨.covers 2059,1,3⟩,⟨.covers 147,1,2⟩,⟨.covers 99,1,5⟩,⟨.covers 2307,1,1⟩,⟨.covers 1539,1,7⟩,⟨.covers 525,1,19⟩,⟨.covers 1037,1,19⟩,⟨.covers 149,1,7⟩,⟨.covers 197,1,4⟩,⟨.covers 773,1,19⟩,⟨.covers 1541,1,19⟩,⟨.covers 1049,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 3081,1,13⟩,⟨.covers 2097,1,1⟩,⟨.covers 657,1,1⟩,⟨.covers 353,1,1⟩,⟨.covers 2145,1,1⟩,⟨.covers 449,1,5⟩,⟨.covers 1793,1,6⟩,⟨.covers 3329,1,2⟩,⟨.covers 78,1,7⟩,⟨.covers 526,1,3⟩,⟨.covers 2062,1,6⟩,⟨.covers 54,1,2⟩,⟨.covers 774,1,11⟩,⟨.covers 3078,1,1⟩,⟨.covers 2098,1,2⟩,⟨.covers 1106,1,9⟩,⟨.covers 2194,1,5⟩,⟨.covers 610,1,2⟩,⟨.covers 108,1,4⟩,⟨.covers 2316,1,7⟩,⟨.covers 1548,1,3⟩,⟨.covers 308,1,2⟩,⟨.covers 1124,1,1⟩,⟨.covers 1220,1,4⟩,⟨.covers 2244,1,1⟩,⟨.covers 1796,1,3⟩,⟨.covers 3332,1,5⟩,⟨.covers 184,1,4⟩,⟨.covers 568,1,1⟩,⟨.covers 344,1,9⟩,⟨.covers 1112,1,2⟩,⟨.covers 664,1,3⟩,⟨.covers 3144,1,1⟩,⟨.covers 2824,1,19⟩,⟨.covers 3592,1,19⟩,⟨.covers 2352,1,5⟩,⟨.covers 1584,1,4⟩,⟨.covers 2608,1,4⟩,⟨.covers 1808,1,7⟩,⟨.covers 3344,1,8⟩,⟨.covers 1248,1,4⟩,⟨.covers 864,1,2⟩,⟨.covers 2496,1,2⟩,⟨.covers 2752,1,7⟩]
def bound : Int := 20

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_009
namespace C13.Global.FastDual64_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,5,9]
def points : Finset C13.Point := {0,3,5,9}
def columns : List Code := [253,702,727,764,830,892,956,967,979,981,1207,1246,1269,1374,1447,1461,1494,1498,1500,1509,1654,1691,1693,1747,1749,1753,1766,1780,1852,1894,1908,1945,1987,2001,2297,2411,2413,2425,2518,2537,2647,2734,2746,2771,2773,2794,2808,2862,2876,2887,2901,2986,3000,3011,3025,3127,3187,3251,3278,3286,3290,3292,3313,3367,3379,3381,3406,3414,3418,3420,3427,3429,3433,3441,3478,3491,3493,3505,3526,3530,3532,3538,3540,3544,3553,3669,3686,3737,3754,3793,3810,3824]
def rows : List LinearRow := [⟨.covers 43,1,12⟩,⟨.covers 139,1,25⟩,⟨.covers 525,1,6⟩,⟨.covers 2061,1,25⟩,⟨.covers 57,1,19⟩,⟨.covers 777,1,6⟩,⟨.covers 1289,1,19⟩,⟨.covers 2569,1,6⟩,⟨.covers 78,1,6⟩,⟨.covers 58,1,25⟩,⟨.covers 106,1,12⟩,⟨.covers 202,1,6⟩,⟨.covers 3082,1,6⟩,⟨.covers 1292,1,6⟩,⟨.covers 1548,1,19⟩,⟨.covers 2572,1,25⟩,⟨.covers 344,1,6⟩,⟨.covers 1112,1,6⟩,⟨.covers 232,1,6⟩,⟨.covers 1224,1,6⟩,⟨.covers 3336,1,6⟩,⟨.covers 3592,1,19⟩,⟨.covers 928,1,25⟩,⟨.incident 3,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_010
namespace C13.Global.FastDual64_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,5,10]
def points : Finset C13.Point := {0,3,5,10}
def columns : List Code := [253,702,727,764,830,892,956,967,979,981,982,1207,1246,1269,1374,1447,1461,1498,1500,1509,1654,1691,1693,1753,1754,1756,1766,1780,1882,1894,1945,1957,2008,2020,2297,2411,2413,2425,2518,2537,2647,2734,2746,2771,2773,2774,2794,2808,2862,2874,2876,2887,2899,2901,2902,2921,2922,2924,2936,2966,2986,2988,3000,3011,3013,3014,3025,3026,3028,3048,3127,3187,3251,3278,3290,3292,3313,3367,3379,3406,3418,3493,3505,3532,3544,3635,3686,3698,3737,3788,3800,3824]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 43,1,1⟩,⟨.covers 139,1,2⟩,⟨.covers 83,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 163,1,2⟩,⟨.covers 2061,1,2⟩,⟨.covers 1541,1,2⟩,⟨.covers 3077,1,2⟩,⟨.covers 57,1,2⟩,⟨.covers 777,1,1⟩,⟨.covers 1289,1,1⟩,⟨.covers 449,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 3585,1,2⟩,⟨.covers 1328,1,2⟩,⟨.incident 0,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_011
namespace C13.Global.FastDual64_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,5,11]
def points : Finset C13.Point := {0,3,5,11}
def columns : List Code := [253,702,727,764,830,892,956,967,979,981,982,1207,1246,1269,1374,1447,1461,1494,1498,1500,1509,1654,1687,1691,1693,1694,1718,1747,1749,1750,1753,1754,1756,1766,1780,1822,1846,1852,1878,1882,1884,1894,1908,1927,1939,1941,1942,1945,1946,1948,1957,1958,1972,1987,1989,1990,2001,2002,2004,2008,2020,2297,2411,2413,2425,2518,2537,2647,2734,2746,2773,2774,2794,2808,2901,2921,2966,2986,3028,3048,3127,3187,3251,3278,3286,3292,3313,3379,3433,3441,3478,3532,3540,3607,3635,3669,3726,3734,3754,3762,3788,3796,3824,3853,3861,3881,3889,3980,3988,4008,4016]
def rows : List LinearRow := [⟨.covers 39,1,17⟩,⟨.covers 71,1,9⟩,⟨.covers 2055,1,11⟩,⟨.covers 43,1,13⟩,⟨.covers 139,1,72⟩,⟨.covers 163,1,28⟩,⟨.covers 2563,1,23⟩,⟨.covers 141,1,35⟩,⟨.covers 525,1,19⟩,⟨.covers 533,1,2⟩,⟨.covers 2117,1,5⟩,⟨.covers 1157,1,7⟩,⟨.covers 705,1,37⟩,⟨.covers 897,1,34⟩,⟨.covers 46,1,17⟩,⟨.covers 78,1,9⟩,⟨.covers 526,1,4⟩,⟨.covers 2062,1,5⟩,⟨.covers 58,1,25⟩,⟨.covers 3082,1,27⟩,⟨.covers 2098,1,2⟩,⟨.covers 1106,1,1⟩,⟨.covers 1298,1,8⟩,⟨.covers 2322,1,17⟩,⟨.covers 610,1,23⟩,⟨.covers 1122,1,27⟩,⟨.covers 2594,1,5⟩,⟨.covers 706,1,3⟩,⟨.covers 898,1,5⟩,⟨.covers 2434,1,16⟩,⟨.covers 540,1,7⟩,⟨.covers 2124,1,8⟩,⟨.covers 1164,1,2⟩,⟨.covers 180,1,13⟩,⟨.covers 308,1,13⟩,⟨.covers 404,1,7⟩,⟨.covers 2196,1,5⟩,⟨.covers 420,1,13⟩,⟨.covers 1572,1,5⟩,⟨.covers 1604,1,2⟩,⟨.covers 2628,1,3⟩,⟨.covers 3140,1,5⟩,⟨.covers 3588,1,17⟩,⟨.covers 1112,1,35⟩,⟨.covers 1304,1,38⟩,⟨.covers 624,1,25⟩,⟨.covers 1328,1,3⟩,⟨.covers 848,1,9⟩,⟨.covers 2384,1,13⟩,⟨.covers 2832,1,21⟩,⟨.covers 1248,1,23⟩,⟨.covers 864,1,13⟩,⟨.covers 1376,1,13⟩,⟨.covers 928,1,5⟩,⟨.covers 1472,1,9⟩,⟨.covers 2496,1,13⟩,⟨.covers 3456,1,18⟩,⟨.incident 0,8,18⟩,⟨.incident 3,8,16⟩,⟨.incident 5,8,23⟩,⟨.incident 11,8,35⟩]
def bound : Int := 107

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_012
namespace C13.Global.FastDual64_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,7,9]
def points : Finset C13.Point := {0,3,7,9}
def columns : List Code := [382,487,830,886,892,967,979,995,1374,1398,1402,1404,1447,1461,1509,1654,1691,1693,1721,1753,1852,1894,1908,1945,1987,2001,2167,2286,2407,2411,2413,2414,2419,2421,2422,2425,2426,2428,2486,2518,2534,2647,2677,2678,2734,2746,2794,2862,2876,2887,2901,2918,2932,2986,3011,3042,3127,3187,3189,3190,3278,3292,3308,3367,3379,3381,3382,3406,3414,3418,3420,3427,3429,3430,3433,3434,3436,3441,3442,3444,3448,3478,3493,3494,3508,3526,3532,3540,3556,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 135,1,8⟩,⟨.covers 1031,1,3⟩,⟨.covers 43,1,11⟩,⟨.covers 139,1,11⟩,⟨.covers 83,1,3⟩,⟨.covers 2563,1,8⟩,⟨.covers 45,1,11⟩,⟨.covers 141,1,3⟩,⟨.covers 53,1,3⟩,⟨.covers 197,1,3⟩,⟨.covers 1541,1,8⟩,⟨.covers 3077,1,3⟩,⟨.covers 169,1,11⟩,⟨.covers 201,1,11⟩,⟨.covers 2569,1,11⟩,⟨.covers 113,1,6⟩,⟨.covers 1793,1,3⟩,⟨.covers 2817,1,3⟩,⟨.covers 3329,1,6⟩,⟨.covers 526,1,8⟩,⟨.covers 1038,1,3⟩,⟨.covers 58,1,3⟩,⟨.covers 202,1,8⟩,⟨.covers 2194,1,3⟩,⟨.covers 1298,1,3⟩,⟨.covers 3090,1,3⟩,⟨.covers 1570,1,3⟩,⟨.covers 92,1,3⟩,⟨.covers 1292,1,3⟩,⟨.covers 2572,1,3⟩,⟨.covers 180,1,8⟩,⟨.covers 212,1,8⟩,⟨.covers 1796,1,8⟩,⟨.covers 120,1,6⟩,⟨.covers 232,1,3⟩,⟨.covers 3336,1,6⟩,⟨.covers 624,1,3⟩,⟨.covers 912,1,8⟩,⟨.covers 2832,1,8⟩,⟨.covers 1248,1,8⟩,⟨.covers 928,1,11⟩,⟨.covers 3616,1,8⟩,⟨.covers 3456,1,3⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_013
namespace C13.Global.FastDual64_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,7,10]
def points : Finset C13.Point := {0,3,7,10}
def columns : List Code := [382,487,830,886,890,892,967,979,995,1374,1398,1402,1447,1461,1509,1654,1691,1693,1721,1753,1882,1894,1906,1945,1957,1969,2167,2286,2407,2411,2413,2414,2419,2421,2422,2425,2426,2428,2486,2518,2534,2647,2675,2677,2678,2734,2746,2794,2862,2870,2874,2876,2887,2899,2901,2902,2915,2917,2918,2921,2922,2924,2929,2930,2932,2936,2966,2982,2986,2994,3011,3014,3026,3042,3127,3187,3190,3278,3292,3308,3367,3379,3406,3418,3430,3442,3493,3532,3556,3635,3686,3698,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 519,1,1⟩,⟨.covers 43,1,1⟩,⟨.covers 163,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 1289,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 58,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 3344,1,1⟩,⟨.covers 1248,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_014
namespace C13.Global.FastDual64_015
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,3,7,11]
def points : Finset C13.Point := {0,3,7,11}
def columns : List Code := [382,487,830,886,890,892,967,979,995,1374,1398,1402,1404,1447,1461,1509,1654,1691,1693,1721,1753,1822,1846,1850,1852,1878,1882,1884,1894,1906,1908,1912,1927,1939,1941,1945,1955,1957,1969,1987,1989,2001,2017,2167,2286,2411,2413,2419,2421,2425,2486,2518,2647,2675,2677,2734,2746,2794,2901,2921,2929,2966,2986,2994,3127,3187,3189,3278,3292,3308,3379,3433,3441,3478,3532,3540,3607,3635,3669,3697,3726,3754,3788,3816,3853,3861,3881,3889,3980,3988,4008,4016]
def rows : List LinearRow := [⟨.covers 43,1,1⟩,⟨.covers 45,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 57,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 154,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 2752,1,1⟩,⟨.incident 3,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source64.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source64.rootCodes link64 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual64_015
