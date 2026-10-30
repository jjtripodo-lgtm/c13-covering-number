import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source65
namespace C13.Global.FastDual65_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,5,9,10]
def points : Finset C13.Point := {0,5,9,10}
def columns : List Code := [239,253,478,493,638,702,719,727,731,733,750,764,830,878,892,942,956,967,971,979,981,985,1199,1207,1246,1269,1374,1447,1453,1461,1486,1498,1500,1509,1646,1654,1679,1691,1693,1753,1766,1780,1894,1945,2159,2171,2270,2297,2398,2411,2413,2425,2462,2510,2518,2522,2524,2537,2622,2639,2647,2653,2670,2734,2746,2771,2773,2777,2794,2808,2862,2876,2887,2901,2986,3000,3011,3025,3119,3127,3131,3166,3187,3251,3278,3290,3292,3313,3367,3379,3406,3418,3493,3505,3532,3544,3599,3686,3737,3824]
def rows : List LinearRow := [⟨.covers 71,1,16⟩,⟨.covers 139,1,22⟩,⟨.covers 83,1,22⟩,⟨.covers 147,1,8⟩,⟨.covers 99,1,6⟩,⟨.covers 163,1,8⟩,⟨.covers 387,1,22⟩,⟨.covers 77,1,6⟩,⟨.covers 53,1,9⟩,⟨.covers 533,1,5⟩,⟨.covers 773,1,18⟩,⟨.covers 1541,1,9⟩,⟨.covers 57,1,6⟩,⟨.covers 297,1,12⟩,⟨.covers 329,1,15⟩,⟨.covers 2121,1,13⟩,⟨.covers 2569,1,19⟩,⟨.covers 209,1,7⟩,⟨.covers 2577,1,11⟩,⟨.covers 353,1,7⟩,⟨.covers 1793,1,30⟩,⟨.covers 2817,1,36⟩,⟨.covers 3329,1,32⟩,⟨.covers 46,1,3⟩,⟨.covers 78,1,5⟩,⟨.covers 54,1,8⟩,⟨.covers 2070,1,16⟩,⟨.covers 390,1,3⟩,⟨.covers 2182,1,45⟩,⟨.covers 58,1,25⟩,⟨.covers 1050,1,1⟩,⟨.covers 1098,1,20⟩,⟨.covers 1106,1,4⟩,⟨.covers 2194,1,2⟩,⟨.covers 2210,1,15⟩,⟨.covers 2594,1,5⟩,⟨.covers 706,1,12⟩,⟨.covers 1794,1,28⟩,⟨.covers 3586,1,3⟩,⟨.covers 540,1,12⟩,⟨.covers 1292,1,20⟩,⟨.covers 116,1,16⟩,⟨.covers 308,1,21⟩,⟨.covers 404,1,2⟩,⟨.covers 2196,1,47⟩,⟨.covers 3140,1,3⟩,⟨.covers 184,1,21⟩,⟨.covers 1112,1,23⟩,⟨.covers 232,1,6⟩,⟨.covers 360,1,19⟩,⟨.covers 2824,1,35⟩,⟨.covers 3336,1,25⟩,⟨.covers 736,1,11⟩,⟨.covers 2656,1,16⟩,⟨.covers 928,1,12⟩,⟨.covers 1472,1,25⟩,⟨.incident 0,8,19⟩,⟨.incident 5,8,22⟩,⟨.incident 9,8,24⟩,⟨.incident 10,8,40⟩]
def bound : Int := 115

theorem column_mask : listMask columns = restrictMask universeMask Source65.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source65.rootCodes link65 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual65_008
namespace C13.Global.FastDual65_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,5,9,11]
def points : Finset C13.Point := {0,5,9,11}
def columns : List Code := [239,253,478,493,638,702,719,727,731,733,750,764,830,878,892,942,956,967,971,979,981,985,1199,1207,1246,1269,1374,1438,1447,1453,1461,1486,1494,1498,1500,1509,1598,1646,1654,1679,1691,1693,1710,1747,1749,1753,1766,1780,1838,1852,1894,1908,1931,1945,1987,2001,2159,2171,2270,2297,2411,2413,2425,2462,2510,2518,2524,2537,2639,2647,2653,2734,2746,2773,2794,2808,2901,2986,3119,3127,3131,3187,3230,3251,3278,3286,3292,3313,3371,3379,3433,3441,3470,3478,3532,3540,3599,3669,3754,3824]
def rows : List LinearRow := [⟨.covers 39,1,7⟩,⟨.covers 71,1,25⟩,⟨.covers 139,1,19⟩,⟨.covers 83,1,3⟩,⟨.covers 147,1,27⟩,⟨.covers 99,1,2⟩,⟨.covers 163,1,1⟩,⟨.covers 323,1,25⟩,⟨.covers 2307,1,7⟩,⟨.covers 141,1,8⟩,⟨.covers 525,1,3⟩,⟨.covers 1037,1,1⟩,⟨.covers 53,1,6⟩,⟨.covers 293,1,15⟩,⟨.covers 389,1,7⟩,⟨.covers 1157,1,3⟩,⟨.covers 1541,1,16⟩,⟨.covers 57,1,16⟩,⟨.covers 537,1,6⟩,⟨.covers 777,1,14⟩,⟨.covers 177,1,3⟩,⟨.covers 209,1,2⟩,⟨.covers 1553,1,10⟩,⟨.covers 3089,1,3⟩,⟨.covers 417,1,15⟩,⟨.covers 1793,1,32⟩,⟨.covers 2817,1,29⟩,⟨.covers 54,1,19⟩,⟨.covers 2182,1,27⟩,⟨.covers 58,1,13⟩,⟨.covers 1050,1,2⟩,⟨.covers 1098,1,47⟩,⟨.covers 1106,1,14⟩,⟨.covers 1122,1,12⟩,⟨.covers 1570,1,4⟩,⟨.covers 706,1,7⟩,⟨.covers 2818,1,27⟩,⟨.covers 3330,1,20⟩,⟨.covers 3586,1,9⟩,⟨.covers 540,1,18⟩,⟨.covers 2316,1,20⟩,⟨.covers 116,1,14⟩,⟨.covers 2196,1,27⟩,⟨.covers 228,1,9⟩,⟨.covers 420,1,18⟩,⟨.covers 1188,1,4⟩,⟨.covers 184,1,14⟩,⟨.covers 312,1,14⟩,⟨.covers 1112,1,47⟩,⟨.covers 3336,1,7⟩,⟨.covers 2352,1,4⟩,⟨.covers 1808,1,2⟩,⟨.covers 864,1,18⟩,⟨.covers 2656,1,13⟩,⟨.covers 1696,1,14⟩,⟨.covers 1824,1,29⟩,⟨.covers 2496,1,20⟩,⟨.covers 3392,1,27⟩,⟨.incident 0,8,19⟩,⟨.incident 5,8,20⟩,⟨.incident 9,8,26⟩,⟨.incident 11,8,36⟩]
def bound : Int := 111

theorem column_mask : listMask columns = restrictMask universeMask Source65.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source65.rootCodes link65 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual65_009
namespace C13.Global.FastDual65_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,5,10,11]
def points : Finset C13.Point := {0,5,10,11}
def columns : List Code := [239,253,478,493,638,702,719,727,731,733,734,750,764,830,862,878,892,926,942,956,967,971,973,974,979,981,982,985,986,988,1004,1199,1207,1246,1269,1374,1447,1453,1461,1486,1498,1500,1509,1630,1646,1654,1679,1691,1693,1742,1753,1754,1756,1766,1780,1870,1882,1894,1933,1945,1957,1996,2008,2020,2159,2171,2270,2297,2411,2413,2425,2462,2510,2518,2524,2537,2639,2647,2653,2718,2734,2746,2766,2773,2774,2780,2794,2808,2893,2901,2921,2958,2966,2986,3020,3028,3048,3119,3127,3131,3187,3251,3278,3292,3313,3379,3532,3599,3635,3788,3824]
def rows : List LinearRow := [⟨.covers 71,1,24⟩,⟨.covers 139,1,17⟩,⟨.covers 83,1,13⟩,⟨.covers 147,1,13⟩,⟨.covers 323,1,15⟩,⟨.covers 387,1,22⟩,⟨.covers 525,1,9⟩,⟨.covers 533,1,4⟩,⟨.covers 293,1,2⟩,⟨.covers 2309,1,25⟩,⟨.covers 89,1,2⟩,⟨.covers 537,1,9⟩,⟨.covers 297,1,5⟩,⟨.covers 1289,1,23⟩,⟨.covers 705,1,5⟩,⟨.covers 1793,1,16⟩,⟨.covers 2817,1,12⟩,⟨.covers 3329,1,13⟩,⟨.covers 54,1,13⟩,⟨.covers 86,1,9⟩,⟨.covers 166,1,3⟩,⟨.covers 390,1,2⟩,⟨.covers 2182,1,33⟩,⟨.covers 58,1,13⟩,⟨.covers 154,1,9⟩,⟨.covers 106,1,3⟩,⟨.covers 330,1,9⟩,⟨.covers 1098,1,39⟩,⟨.covers 610,1,8⟩,⟨.covers 674,1,14⟩,⟨.covers 1570,1,5⟩,⟨.covers 2594,1,8⟩,⟨.covers 706,1,3⟩,⟨.covers 1794,1,9⟩,⟨.covers 540,1,5⟩,⟨.covers 556,1,5⟩,⟨.covers 116,1,26⟩,⟨.covers 308,1,21⟩,⟨.covers 404,1,7⟩,⟨.covers 2196,1,40⟩,⟨.covers 1604,1,3⟩,⟨.covers 2628,1,5⟩,⟨.covers 184,1,20⟩,⟨.covers 312,1,24⟩,⟨.covers 1112,1,32⟩,⟨.covers 1672,1,5⟩,⟨.covers 2696,1,3⟩,⟨.covers 2824,1,4⟩,⟨.covers 3336,1,72⟩,⟨.covers 3592,1,28⟩,⟨.covers 2832,1,9⟩,⟨.covers 736,1,22⟩,⟨.covers 1376,1,28⟩,⟨.covers 2464,1,27⟩,⟨.covers 1824,1,11⟩,⟨.covers 2848,1,10⟩,⟨.covers 3648,1,26⟩,⟨.incident 0,8,35⟩,⟨.incident 5,8,24⟩,⟨.incident 10,8,18⟩,⟨.incident 11,8,16⟩]
def bound : Int := 107

theorem column_mask : listMask columns = restrictMask universeMask Source65.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source65.rootCodes link65 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual65_010
namespace C13.Global.FastDual65_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,6,9,10]
def points : Finset C13.Point := {0,6,9,10}
def columns : List Code := [239,446,491,702,719,727,830,942,954,956,967,971,979,995,1150,1199,1207,1211,1213,1246,1262,1374,1390,1402,1447,1453,1459,1461,1465,1486,1498,1646,1654,1679,1691,1693,1721,1766,1894,1945,2159,2173,2238,2366,2411,2413,2425,2462,2478,2486,2490,2492,2537,2622,2639,2647,2653,2677,2734,2746,2748,2773,2862,2876,2887,2901,2986,3000,3011,3025,3119,3127,3131,3166,3182,3251,3253,3257,3278,3292,3308,3367,3379,3406,3418,3493,3505,3532,3544,3599,3686,3737]
def rows : List LinearRow := [⟨.covers 83,1,1⟩,⟨.covers 773,1,1⟩,⟨.covers 1793,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 2608,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 864,1,1⟩,⟨.covers 3616,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 2752,1,1⟩,⟨.incident 9,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source65.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source65.rootCodes link65 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual65_011
namespace C13.Global.FastDual65_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,6,9,11]
def points : Finset C13.Point := {0,6,9,11}
def columns : List Code := [239,446,491,702,719,727,830,942,954,956,967,971,979,995,1150,1199,1207,1211,1213,1214,1246,1262,1342,1374,1390,1402,1438,1447,1451,1453,1454,1459,1461,1462,1465,1466,1468,1486,1498,1514,1598,1646,1654,1679,1691,1693,1710,1721,1722,1724,1766,1838,1852,1894,1931,1945,1962,1976,1987,2018,2159,2173,2238,2411,2413,2425,2462,2478,2486,2490,2537,2639,2647,2653,2677,2734,2746,2773,2901,2986,3119,3127,3131,3230,3246,3251,3254,3258,3278,3292,3308,3371,3379,3433,3470,3478,3498,3506,3532,3560,3599,3669,3754]
def rows : List LinearRow := [⟨.covers 39,1,2⟩,⟨.covers 1031,1,3⟩,⟨.covers 2059,1,2⟩,⟨.covers 83,1,13⟩,⟨.covers 1043,1,1⟩,⟨.covers 99,1,6⟩,⟨.covers 323,1,1⟩,⟨.covers 2307,1,4⟩,⟨.covers 2563,1,6⟩,⟨.covers 525,1,6⟩,⟨.covers 1037,1,3⟩,⟨.covers 293,1,3⟩,⟨.covers 89,1,13⟩,⟨.covers 777,1,13⟩,⟨.covers 1793,1,1⟩,⟨.covers 2817,1,20⟩,⟨.covers 3329,1,8⟩,⟨.covers 582,1,1⟩,⟨.covers 2182,1,1⟩,⟨.covers 774,1,12⟩,⟨.covers 2818,1,20⟩,⟨.covers 1292,1,3⟩,⟨.covers 2316,1,10⟩,⟨.covers 308,1,3⟩,⟨.covers 404,1,3⟩,⟨.covers 216,1,8⟩,⟨.covers 1136,1,8⟩,⟨.covers 688,1,9⟩,⟨.covers 2224,1,7⟩,⟨.covers 1584,1,5⟩,⟨.covers 2704,1,3⟩,⟨.covers 3216,1,5⟩,⟨.covers 3344,1,1⟩,⟨.covers 3600,1,20⟩,⟨.covers 736,1,1⟩,⟨.covers 2272,1,13⟩,⟨.covers 864,1,1⟩,⟨.covers 2656,1,20⟩,⟨.covers 3616,1,20⟩,⟨.covers 1728,1,12⟩,⟨.covers 2752,1,16⟩,⟨.incident 9,8,-6⟩,⟨.incident 11,8,-6⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source65.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source65.rootCodes link65 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual65_012
namespace C13.Global.FastDual65_013
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,6,10,11]
def points : Finset C13.Point := {0,6,10,11}
def columns : List Code := [239,446,491,702,719,727,830,926,942,950,954,956,967,971,979,995,1150,1199,1207,1211,1213,1246,1262,1374,1390,1402,1447,1453,1459,1461,1465,1486,1498,1630,1646,1654,1679,1691,1693,1715,1717,1721,1742,1766,1870,1882,1894,1906,1933,1945,1957,1969,2159,2173,2238,2411,2413,2425,2462,2478,2486,2490,2537,2639,2647,2653,2677,2718,2734,2742,2746,2773,2893,2901,2921,2929,2958,2966,2986,2994,3119,3127,3131,3251,3278,3292,3308,3379,3532,3599,3635,3788]
def rows : List LinearRow := [⟨.covers 2307,1,1⟩,⟨.covers 2309,1,2⟩,⟨.covers 3077,1,1⟩,⟨.covers 89,1,2⟩,⟨.covers 3329,1,1⟩,⟨.covers 2070,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 2818,1,1⟩,⟨.covers 2224,1,1⟩,⟨.covers 3152,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 3600,1,2⟩,⟨.covers 2656,1,2⟩,⟨.covers 3168,1,2⟩,⟨.covers 2496,1,2⟩,⟨.covers 2752,1,2⟩,⟨.incident 11,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source65.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source65.rootCodes link65 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual65_013
namespace C13.Global.FastDual65_014
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,9,10,11]
def points : Finset C13.Point := {0,9,10,11}
def columns : List Code := [239,247,251,253,254,382,446,478,487,491,493,494,499,501,502,505,506,508,638,702,719,727,731,733,750,755,757,758,761,762,764,830,878,886,892,942,954,956,967,971,979,981,985,995,998,1002,1009,1010,1012,1016,1150,1199,1207,1211,1213,1246,1262,1267,1269,1270,1273,1274,1276,1374,1390,1398,1402,1447,1453,1459,1461,1465,1486,1498,1500,1509,1510,1516,1521,1522,1524,1528,1646,1654,1679,1691,1693,1721,1753,1766,1777,1778,1780,1784,1894,1945,2032,2159,2167,2171,2173,2238,2270,2286,2291,2293,2294,2297,2298,2300,2411,2413,2419,2421,2425,2462,2478,2486,2490,2510,2518,2524,2537,2538,2540,2545,2546,2548,2552,2639,2647,2653,2677,2734,2746,2773,2794,2801,2802,2804,2808,2901,2986,3056,3119,3127,3131,3187,3251,3278,3292,3308,3313,3314,3316,3320,3379,3532,3568,3599,3824]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 71,1,1⟩,⟨.covers 43,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 83,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 323,1,1⟩,⟨.covers 387,1,1⟩,⟨.covers 77,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 53,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 293,1,1⟩,⟨.covers 389,1,1⟩,⟨.covers 57,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 297,1,1⟩,⟨.covers 329,1,1⟩,⟨.covers 225,1,2⟩,⟨.covers 1793,1,3⟩,⟨.covers 2070,1,1⟩,⟨.covers 2182,1,2⟩,⟨.covers 1050,1,1⟩,⟨.covers 1098,1,2⟩,⟨.covers 1106,1,2⟩,⟨.covers 2194,1,2⟩,⟨.covers 706,1,1⟩,⟨.covers 1794,1,4⟩,⟨.covers 2818,1,4⟩,⟨.covers 540,1,1⟩,⟨.covers 556,1,2⟩,⟨.covers 564,1,2⟩,⟨.covers 2196,1,2⟩,⟨.covers 1188,1,1⟩,⟨.covers 568,1,2⟩,⟨.covers 1112,1,2⟩,⟨.covers 2152,1,1⟩,⟨.covers 3336,1,4⟩,⟨.covers 2832,1,3⟩,⟨.covers 3344,1,3⟩,⟨.covers 3600,1,1⟩,⟨.incident 0,8,1⟩,⟨.incident 9,8,3⟩,⟨.incident 10,8,3⟩,⟨.incident 11,8,3⟩]
def bound : Int := 10

theorem column_mask : listMask columns = restrictMask universeMask Source65.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source65.rootCodes link65 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual65_014
namespace C13.Global.FastDual65_015
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,9,10]
def points : Finset C13.Point := {3,6,9,10}
def columns : List Code := [379,439,631,699,701,702,727,743,829,830,855,871,953,954,956,967,979,995,1207,1246,1335,1371,1374,1402,1447,1459,1461,1498,1639,1654,1691,1693,1721,1766,1894,1945,2231,2285,2359,2411,2413,2425,2455,2471,2483,2485,2486,2537,2647,2663,2677,2731,2734,2745,2746,2748,2759,2773,2862,2876,2887,2901,2986,3000,3011,3025,3127,3239,3251,3253,3277,3278,3292,3308,3367,3379,3406,3418,3493,3505,3532,3544,3686,3737]
def rows : List LinearRow := [⟨.covers 1037,1,1⟩,⟨.covers 773,1,1⟩,⟨.covers 1289,1,1⟩,⟨.covers 1793,1,1⟩,⟨.covers 3585,1,2⟩,⟨.covers 1546,1,2⟩,⟨.covers 3082,1,1⟩,⟨.covers 1794,1,2⟩,⟨.covers 3586,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 1584,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 928,1,1⟩,⟨.covers 1472,1,1⟩,⟨.covers 1728,1,2⟩,⟨.incident 9,8,-1⟩,⟨.incident 10,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source65.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source65.rootCodes link65 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual65_015
