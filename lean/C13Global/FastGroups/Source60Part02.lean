import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source60
namespace C13.Global.FastDual60_016
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,5,6,10]
def points : Finset C13.Point := {3,5,6,10}
def columns : List Code := [702,727,829,830,855,919,956,967,979,1207,1246,1335,1371,1374,1447,1461,1498,1591,1639,1654,1691,1693,1703,1766,1819,1831,1882,1894,1945,1957,2411,2413,2425,2455,2537,2647,2711,2731,2734,2746,2759,2773,2839,2859,2861,2862,2873,2874,2876,2887,2899,2901,2921,2951,2963,2965,2966,2985,2986,2988,3000,3011,3013,3025,3127,3239,3251,3277,3278,3292,3367,3379,3406,3418,3493,3505,3532,3544,3623,3635,3686,3725,3737,3788,3851,3875,3914,3938,3977,4001,4040,4064]
def rows : List LinearRow := [⟨.covers 99,1,1⟩,⟨.covers 197,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 1292,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 848,1,1⟩,⟨.covers 3152,1,1⟩,⟨.covers 2656,1,1⟩,⟨.incident 6,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_016
namespace C13.Global.FastDual60_017
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,5,6,11]
def points : Finset C13.Point := {3,5,6,11}
def columns : List Code := [702,727,829,830,855,919,956,967,979,1207,1246,1335,1371,1374,1431,1447,1461,1498,1591,1623,1639,1654,1687,1691,1693,1694,1703,1718,1735,1750,1766,1815,1819,1821,1822,1831,1845,1846,1852,1863,1875,1878,1882,1894,1927,1939,1941,1942,1945,1946,1948,1957,1958,1972,1987,1990,2002,2411,2413,2425,2455,2537,2647,2711,2731,2734,2746,2773,2839,2859,2901,2921,2966,2986,3127,3223,3251,3277,3278,3292,3351,3379,3405,3433,3478,3532,3607,3635,3669,3726,3734,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 39,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 141,1,1⟩,⟨.covers 3585,1,1⟩,⟨.covers 2062,1,1⟩,⟨.covers 58,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 3330,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 432,1,1⟩,⟨.covers 2384,1,1⟩,⟨.covers 2656,1,1⟩,⟨.covers 3168,1,1⟩,⟨.covers 3232,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 2944,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_017
namespace C13.Global.FastDual60_018
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,5,7,10]
def points : Finset C13.Point := {3,5,7,10}
def columns : List Code := [381,471,829,830,855,892,919,967,979,1143,1245,1335,1371,1374,1383,1447,1461,1509,1591,1639,1654,1691,1693,1753,1819,1831,1882,1894,1945,1957,2391,2411,2413,2425,2455,2503,2518,2647,2731,2734,2746,2794,2839,2859,2861,2862,2873,2874,2876,2887,2899,2901,2902,2921,2922,2924,2936,2951,2963,2966,2986,3011,3014,3026,3127,3175,3187,3277,3278,3292,3367,3379,3406,3418,3493,3532,3623,3635,3686,3698,3725,3737,3788,3800,3851,3875,3914,3938,3977,4001,4040,4064]
def rows : List LinearRow := [⟨.covers 135,1,6⟩,⟨.covers 139,1,19⟩,⟨.covers 147,1,6⟩,⟨.covers 163,1,6⟩,⟨.covers 201,1,25⟩,⟨.covers 142,1,12⟩,⟨.covers 166,1,13⟩,⟨.covers 198,1,6⟩,⟨.covers 178,1,25⟩,⟨.covers 210,1,6⟩,⟨.covers 226,1,25⟩,⟨.covers 898,1,6⟩,⟨.covers 2434,1,6⟩,⟨.covers 1548,1,25⟩,⟨.covers 180,1,25⟩,⟨.covers 228,1,25⟩,⟨.covers 2436,1,6⟩,⟨.covers 912,1,6⟩,⟨.covers 3216,1,25⟩,⟨.covers 1920,1,19⟩,⟨.covers 3456,1,6⟩,⟨.incident 7,8,-25⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_018
namespace C13.Global.FastDual60_019
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,5,7,11]
def points : Finset C13.Point := {3,5,7,11}
def columns : List Code := [381,471,829,830,855,892,919,967,979,1143,1245,1335,1367,1371,1373,1374,1383,1397,1431,1447,1461,1479,1493,1509,1591,1623,1639,1654,1691,1693,1753,1815,1819,1821,1822,1831,1845,1846,1852,1863,1875,1877,1878,1881,1882,1884,1893,1894,1908,1927,1939,1941,1945,1957,1987,1989,2001,2391,2411,2413,2425,2455,2518,2647,2731,2734,2746,2794,2839,2859,2901,2921,2966,2986,3127,3159,3187,3277,3278,3292,3351,3379,3405,3413,3433,3441,3478,3532,3540,3607,3635,3669,3726,3754,3788]
def rows : List LinearRow := [⟨.covers 39,1,4⟩,⟨.covers 135,1,4⟩,⟨.covers 519,1,1⟩,⟨.covers 2055,1,7⟩,⟨.covers 75,1,7⟩,⟨.covers 1035,1,3⟩,⟨.covers 99,1,3⟩,⟨.covers 163,1,3⟩,⟨.covers 579,1,1⟩,⟨.covers 141,1,3⟩,⟨.covers 525,1,8⟩,⟨.covers 57,1,1⟩,⟨.covers 169,1,8⟩,⟨.covers 3081,1,8⟩,⟨.covers 3585,1,3⟩,⟨.covers 46,1,6⟩,⟨.covers 78,1,10⟩,⟨.covers 1038,1,1⟩,⟨.covers 582,1,2⟩,⟨.covers 774,1,3⟩,⟨.covers 1546,1,4⟩,⟨.covers 114,1,4⟩,⟨.covers 178,1,11⟩,⟨.covers 210,1,7⟩,⟨.covers 226,1,11⟩,⟨.covers 834,1,1⟩,⟨.covers 3330,1,4⟩,⟨.covers 108,1,8⟩,⟨.covers 172,1,4⟩,⟨.covers 2316,1,3⟩,⟨.covers 180,1,11⟩,⟨.covers 228,1,11⟩,⟨.covers 804,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 216,1,8⟩,⟨.covers 1800,1,3⟩,⟨.covers 2160,1,1⟩,⟨.covers 2352,1,7⟩,⟨.covers 1584,1,5⟩,⟨.covers 2256,1,3⟩,⟨.covers 912,1,2⟩,⟨.covers 3168,1,3⟩,⟨.covers 928,1,5⟩,⟨.covers 2464,1,5⟩,⟨.covers 3232,1,4⟩,⟨.covers 1824,1,1⟩,⟨.covers 3616,1,2⟩,⟨.covers 2496,1,1⟩,⟨.covers 1728,1,3⟩,⟨.covers 1856,1,3⟩,⟨.covers 2880,1,11⟩,⟨.covers 3648,1,8⟩,⟨.covers 1920,1,3⟩,⟨.covers 3456,1,7⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_019
namespace C13.Global.FastDual60_020
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,5,10,11]
def points : Finset C13.Point := {3,5,10,11}
def columns : List Code := [254,381,471,508,702,727,829,830,855,892,919,956,967,979,981,982,1143,1207,1243,1245,1246,1255,1270,1335,1371,1374,1383,1447,1461,1497,1498,1500,1509,1524,1591,1639,1654,1691,1693,1703,1753,1754,1756,1766,1819,1831,1882,1894,1945,1957,2008,2020,2263,2283,2298,2391,2411,2413,2425,2455,2517,2518,2537,2552,2647,2711,2731,2734,2746,2773,2774,2794,2839,2859,2901,2921,2966,2986,3028,3048,3127,3187,3251,3277,3278,3292,3314,3379,3532,3568,3635,3788]
def rows : List LinearRow := [⟨.covers 2061,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 3077,1,1⟩,⟨.covers 169,1,2⟩,⟨.covers 2129,1,1⟩,⟨.covers 3329,1,2⟩,⟨.covers 3585,1,1⟩,⟨.covers 2062,1,1⟩,⟨.covers 2566,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 2314,1,2⟩,⟨.covers 3336,1,2⟩,⟨.covers 3592,1,2⟩,⟨.covers 2608,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 2656,1,2⟩,⟨.covers 3232,1,2⟩,⟨.incident 11,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_020
namespace C13.Global.FastDual60_021
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,10]
def points : Finset C13.Point := {3,6,7,10}
def columns : List Code := [379,439,631,699,823,827,829,830,855,871,883,919,935,947,967,979,995,1335,1371,1374,1402,1447,1461,1591,1639,1654,1691,1693,1721,1819,1831,1843,1882,1894,1906,1945,1957,1969,2359,2411,2413,2425,2455,2471,2486,2615,2647,2663,2677,2731,2734,2746,2839,2855,2859,2861,2862,2867,2869,2870,2873,2874,2876,2887,2899,2901,2915,2917,2921,2929,2951,2963,2966,2979,2982,2986,2994,3011,3127,3277,3278,3292,3308,3367,3379,3406,3418,3493,3532,3623,3635,3686,3725,3737,3788,3851,3875,3914,3938,3977,4001,4040,4064]
def rows : List LinearRow := [⟨.covers 71,1,9⟩,⟨.covers 135,1,7⟩,⟨.covers 75,1,9⟩,⟨.covers 139,1,6⟩,⟨.covers 45,1,11⟩,⟨.covers 2069,1,3⟩,⟨.covers 101,1,3⟩,⟨.covers 169,1,7⟩,⟨.covers 201,1,17⟩,⟨.covers 1289,1,4⟩,⟨.covers 3089,1,4⟩,⟨.covers 46,1,11⟩,⟨.covers 166,1,3⟩,⟨.covers 1286,1,4⟩,⟨.covers 1050,1,1⟩,⟨.covers 106,1,5⟩,⟨.covers 202,1,17⟩,⟨.covers 1546,1,6⟩,⟨.covers 210,1,17⟩,⟨.covers 226,1,17⟩,⟨.covers 3106,1,5⟩,⟨.covers 3330,1,1⟩,⟨.covers 1292,1,9⟩,⟨.covers 1548,1,14⟩,⟨.covers 116,1,2⟩,⟨.covers 180,1,4⟩,⟨.covers 212,1,15⟩,⟨.covers 228,1,17⟩,⟨.covers 1572,1,2⟩,⟨.covers 2628,1,2⟩,⟨.covers 2436,1,4⟩,⟨.covers 1136,1,7⟩,⟨.covers 2160,1,5⟩,⟨.covers 2224,1,4⟩,⟨.covers 2384,1,9⟩,⟨.covers 1616,1,3⟩,⟨.covers 3152,1,2⟩,⟨.covers 1424,1,10⟩,⟨.covers 2704,1,10⟩,⟨.covers 1696,1,4⟩,⟨.covers 3360,1,1⟩,⟨.covers 3616,1,3⟩,⟨.covers 2752,1,1⟩,⟨.covers 1856,1,4⟩,⟨.covers 3456,1,4⟩,⟨.incident 6,8,-3⟩,⟨.incident 7,8,-3⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_021
namespace C13.Global.FastDual60_022
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,7,11]
def points : Finset C13.Point := {3,6,7,11}
def columns : List Code := [379,439,631,699,823,827,829,830,855,871,883,919,935,947,967,979,995,1335,1371,1374,1402,1431,1447,1461,1591,1623,1639,1654,1691,1693,1721,1815,1819,1821,1822,1831,1843,1845,1846,1849,1850,1852,1863,1875,1878,1882,1891,1894,1906,1927,1939,1941,1945,1955,1957,1969,1987,2359,2411,2413,2425,2455,2486,2615,2647,2677,2731,2734,2746,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3277,3278,3292,3308,3351,3379,3405,3433,3478,3532,3607,3635,3669,3726,3754,3788]
def rows : List LinearRow := [⟨.covers 2055,1,1⟩,⟨.covers 1035,1,1⟩,⟨.covers 525,1,1⟩,⟨.covers 169,1,1⟩,⟨.covers 46,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 210,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 180,1,1⟩,⟨.covers 228,1,1⟩,⟨.covers 2824,1,1⟩,⟨.covers 2704,1,1⟩,⟨.covers 3216,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 3616,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_022
namespace C13.Global.FastDual60_023
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [3,6,10,11]
def points : Finset C13.Point := {3,6,10,11}
def columns : List Code := [379,439,631,695,699,701,702,727,743,823,827,829,830,855,871,883,919,935,947,949,950,953,954,956,967,979,995,1207,1246,1335,1371,1374,1402,1447,1459,1461,1498,1591,1639,1654,1691,1693,1703,1715,1717,1721,1766,1819,1831,1843,1882,1894,1906,1945,1957,1969,2231,2285,2359,2411,2413,2425,2455,2483,2486,2537,2615,2647,2677,2711,2731,2734,2739,2742,2746,2773,2839,2859,2867,2901,2921,2929,2966,2986,2994,3127,3251,3277,3278,3292,3308,3379,3532,3635,3788]
def rows : List LinearRow := [⟨.covers 71,1,3⟩,⟨.covers 2055,1,5⟩,⟨.covers 139,1,8⟩,⟨.covers 1035,1,3⟩,⟨.covers 525,1,8⟩,⟨.covers 101,1,5⟩,⟨.covers 2309,1,3⟩,⟨.covers 1541,1,3⟩,⟨.covers 3077,1,5⟩,⟨.covers 1289,1,8⟩,⟨.covers 2569,1,3⟩,⟨.covers 3081,1,5⟩,⟨.covers 3329,1,11⟩,⟨.covers 3585,1,11⟩,⟨.covers 46,1,8⟩,⟨.covers 1286,1,8⟩,⟨.covers 2566,1,3⟩,⟨.covers 106,1,3⟩,⟨.covers 2314,1,8⟩,⟨.covers 3082,1,11⟩,⟨.covers 300,1,3⟩,⟨.covers 116,1,3⟩,⟨.covers 212,1,8⟩,⟨.covers 404,1,3⟩,⟨.covers 420,1,3⟩,⟨.covers 120,1,8⟩,⟨.covers 184,1,3⟩,⟨.covers 3336,1,11⟩,⟨.covers 3592,1,3⟩,⟨.covers 2160,1,3⟩,⟨.covers 1200,1,5⟩,⟨.covers 2224,1,5⟩,⟨.covers 464,1,11⟩,⟨.covers 1616,1,8⟩,⟨.covers 3152,1,3⟩,⟨.covers 2704,1,3⟩,⟨.covers 480,1,11⟩,⟨.covers 3168,1,11⟩,⟨.covers 1696,1,3⟩,⟨.covers 1728,1,8⟩,⟨.covers 1856,1,3⟩,⟨.covers 2880,1,8⟩,⟨.covers 1920,1,3⟩,⟨.covers 2944,1,3⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source60.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source60.rootCodes link60 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual60_023
