import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source59
namespace C13.Global.FastDual59_008
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [2,7,10,11]
def points : Finset C13.Point := {2,7,10,11}
def columns : List Code := [379,439,631,635,637,638,699,731,747,823,827,829,830,859,875,883,885,886,889,890,892,923,939,947,971,979,995,1147,1261,1339,1371,1395,1402,1447,1453,1461,1509,1595,1627,1639,1646,1651,1654,1658,1691,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2171,2270,2363,2411,2419,2425,2455,2462,2486,2518,2619,2647,2653,2667,2675,2677,2681,2731,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3131,3187,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 3329,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 166,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 1796,1,1⟩,⟨.covers 3332,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 1136,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 464,1,1⟩,⟨.covers 1232,1,1⟩,⟨.covers 1616,1,1⟩,⟨.covers 1424,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 480,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 2752,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source59.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source59.rootCodes link59 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual59_008
namespace C13.Global.FastDual59_009
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,5,7,10]
def points : Finset C13.Point := {3,5,7,10}
def columns : List Code := [381,471,829,830,855,892,919,967,979,1143,1245,1335,1371,1374,1383,1447,1461,1509,1591,1639,1654,1691,1693,1753,1819,1831,1882,1894,1945,1957,2391,2411,2413,2425,2455,2503,2518,2647,2731,2734,2746,2794,2839,2859,2861,2862,2873,2874,2876,2887,2899,2901,2902,2921,2922,2924,2936,2951,2963,2966,2986,3011,3014,3026,3127,3175,3187,3277,3278,3292,3367,3379,3406,3418,3493,3532,3623,3635,3686,3698,3725,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 39,1,2⟩,⟨.covers 135,1,3⟩,⟨.covers 2055,1,1⟩,⟨.covers 75,1,7⟩,⟨.covers 147,1,3⟩,⟨.covers 99,1,2⟩,⟨.covers 579,1,3⟩,⟨.covers 45,1,4⟩,⟨.covers 2061,1,2⟩,⟨.covers 57,1,3⟩,⟨.covers 169,1,14⟩,⟨.covers 201,1,2⟩,⟨.covers 3081,1,7⟩,⟨.covers 2097,1,1⟩,⟨.covers 2129,1,2⟩,⟨.covers 2145,1,1⟩,⟨.covers 2817,1,1⟩,⟨.covers 3585,1,2⟩,⟨.covers 78,1,7⟩,⟨.covers 142,1,1⟩,⟨.covers 54,1,6⟩,⟨.covers 166,1,9⟩,⟨.covers 198,1,3⟩,⟨.covers 774,1,1⟩,⟨.covers 58,1,1⟩,⟨.covers 154,1,8⟩,⟨.covers 178,1,6⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,14⟩,⟨.covers 156,1,9⟩,⟨.covers 540,1,2⟩,⟨.covers 108,1,2⟩,⟨.covers 172,1,4⟩,⟨.covers 180,1,14⟩,⟨.covers 2324,1,3⟩,⟨.covers 228,1,6⟩,⟨.covers 1604,1,2⟩,⟨.covers 1800,1,7⟩,⟨.covers 2824,1,2⟩,⟨.covers 2352,1,2⟩,⟨.covers 1584,1,2⟩,⟨.covers 912,1,3⟩,⟨.covers 3216,1,2⟩,⟨.covers 3344,1,7⟩,⟨.covers 864,1,6⟩,⟨.covers 1376,1,1⟩,⟨.covers 3168,1,3⟩,⟨.covers 1696,1,13⟩,⟨.covers 3232,1,14⟩,⟨.covers 3616,1,4⟩,⟨.covers 1472,1,8⟩,⟨.covers 2496,1,3⟩,⟨.covers 1728,1,9⟩,⟨.covers 1920,1,1⟩,⟨.covers 2944,1,3⟩,⟨.incident 5,8,-3⟩,⟨.incident 7,8,-4⟩]
def bound : Int := 8

theorem column_mask : listMask columns = restrictMask universeMask Source59.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source59.rootCodes link59 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual59_009
namespace C13.Global.FastDual59_010
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,5,7,11]
def points : Finset C13.Point := {3,5,7,11}
def columns : List Code := [381,471,829,830,855,892,919,967,979,1143,1245,1335,1367,1371,1373,1374,1383,1397,1431,1447,1461,1479,1493,1509,1591,1623,1639,1654,1691,1693,1753,1815,1819,1821,1822,1831,1845,1846,1852,1863,1875,1877,1878,1881,1882,1884,1893,1894,1908,1927,1939,1941,1945,1957,1987,1989,2001,2391,2411,2413,2425,2455,2518,2647,2731,2734,2746,2794,2839,2859,2901,2921,2966,2986,3127,3159,3187,3277,3278,3292,3351,3379,3405,3413,3433,3441,3478,3532,3540,3607,3635,3669,3726,3754,3788,3853,3861,3881,3889,3980,3988,4008,4016]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 2256,1,1⟩,⟨.covers 1728,1,1⟩,⟨.covers 2944,1,1⟩,⟨.incident 7,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source59.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source59.rootCodes link59 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual59_010
namespace C13.Global.FastDual59_011
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,5,10,11]
def points : Finset C13.Point := {3,5,10,11}
def columns : List Code := [254,381,471,508,702,727,829,830,855,892,919,956,967,979,981,982,1143,1207,1243,1245,1246,1255,1270,1335,1371,1374,1383,1447,1461,1497,1498,1500,1509,1524,1591,1639,1654,1691,1693,1703,1753,1754,1756,1766,1819,1831,1882,1894,1945,1957,2008,2020,2263,2283,2298,2391,2411,2413,2425,2455,2517,2518,2537,2552,2647,2711,2731,2734,2746,2773,2774,2794,2839,2859,2901,2921,2966,2986,3028,3048,3127,3187,3251,3277,3278,3292,3314,3379,3532,3568,3635,3788]
def rows : List LinearRow := [⟨.covers 2055,1,6⟩,⟨.covers 2061,1,12⟩,⟨.covers 2309,1,6⟩,⟨.covers 3077,1,13⟩,⟨.covers 169,1,25⟩,⟨.covers 2129,1,6⟩,⟨.covers 3329,1,25⟩,⟨.covers 3585,1,25⟩,⟨.covers 2062,1,19⟩,⟨.covers 2566,1,6⟩,⟨.covers 3078,1,6⟩,⟨.covers 2314,1,25⟩,⟨.covers 2132,1,6⟩,⟨.covers 2196,1,6⟩,⟨.covers 2820,1,6⟩,⟨.covers 3332,1,25⟩,⟨.covers 3588,1,25⟩,⟨.covers 2224,1,19⟩,⟨.covers 2704,1,6⟩,⟨.covers 2656,1,25⟩,⟨.covers 3232,1,6⟩,⟨.incident 11,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source59.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source59.rootCodes link59 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual59_011
namespace C13.Global.FastDual59_012
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,7,10,11]
def points : Finset C13.Point := {3,7,10,11}
def columns : List Code := [375,379,381,382,439,471,487,631,699,823,827,829,830,855,871,883,885,886,889,890,892,919,935,947,967,979,995,1143,1245,1335,1371,1374,1383,1395,1398,1402,1447,1461,1509,1591,1639,1651,1654,1691,1693,1721,1753,1819,1831,1843,1882,1894,1906,1945,1957,1969,2167,2286,2359,2391,2411,2413,2419,2421,2425,2455,2486,2518,2615,2647,2675,2677,2731,2734,2746,2794,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3187,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 135,1,3⟩,⟨.covers 1031,1,5⟩,⟨.covers 2055,1,5⟩,⟨.covers 75,1,3⟩,⟨.covers 1035,1,8⟩,⟨.covers 77,1,8⟩,⟨.covers 525,1,11⟩,⟨.covers 581,1,3⟩,⟨.covers 2309,1,3⟩,⟨.covers 169,1,3⟩,⟨.covers 2569,1,8⟩,⟨.covers 3081,1,3⟩,⟨.covers 3329,1,11⟩,⟨.covers 3585,1,11⟩,⟨.covers 526,1,11⟩,⟨.covers 582,1,3⟩,⟨.covers 1286,1,3⟩,⟨.covers 106,1,5⟩,⟨.covers 2314,1,3⟩,⟨.covers 1546,1,3⟩,⟨.covers 3082,1,11⟩,⟨.covers 210,1,8⟩,⟨.covers 706,1,3⟩,⟨.covers 1292,1,8⟩,⟨.covers 180,1,8⟩,⟨.covers 1796,1,3⟩,⟨.covers 2820,1,3⟩,⟨.covers 3332,1,3⟩,⟨.covers 3588,1,11⟩,⟨.covers 120,1,3⟩,⟨.covers 184,1,8⟩,⟨.covers 216,1,3⟩,⟨.covers 2160,1,5⟩,⟨.covers 2384,1,3⟩,⟨.covers 1616,1,8⟩,⟨.covers 1424,1,3⟩,⟨.covers 2704,1,3⟩,⟨.covers 3216,1,8⟩,⟨.covers 480,1,8⟩,⟨.covers 1376,1,3⟩,⟨.covers 2656,1,3⟩,⟨.covers 3168,1,5⟩,⟨.covers 2464,1,3⟩,⟨.covers 3232,1,5⟩,⟨.covers 1920,1,8⟩,⟨.covers 2944,1,5⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source59.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source59.rootCodes link59 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual59_012
