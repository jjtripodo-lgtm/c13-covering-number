import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source17
namespace C13.Global.FastDual17_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,8]
def points : Finset C13.Point := {1,3,6,8}
def columns : List Code := [701,743,829,949,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1724,1766,1852,1882,1957,1972,1987,2002,2231,2285,2413,2425,2455,2485,2486,2537,2677,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2773,2789,2861,2876,2921,2951,2966,2981,2996,3011,3041,3127,3251,3253,3254,3277,3292,3308,3418,3433,3448,3478,3493,3508,3623,3635,3637,3638,3669,3685,3686,3700,3725,3733,3737,3740,3747,3749,3750,3753,3754,3756,3761,3762,3764,3768,3781,3788,3796,3812,3854,3884,3914,3944,3974,4004,4034,4064]
def rows : List LinearRow := [⟨.covers 75,1,2⟩,⟨.covers 139,1,2⟩,⟨.covers 1037,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,2⟩,⟨.covers 106,1,2⟩,⟨.covers 202,1,2⟩,⟨.covers 1546,1,1⟩,⟨.covers 92,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 232,1,1⟩,⟨.covers 2384,1,2⟩,⟨.incident 3,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_000
namespace C13.Global.FastDual17_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,9]
def points : Finset C13.Point := {1,3,6,9}
def columns : List Code := [701,743,829,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2231,2285,2413,2425,2455,2483,2485,2486,2537,2677,2731,2734,2745,2746,2748,2773,2876,2901,2986,3000,3011,3025,3127,3251,3253,3254,3277,3292,3308,3351,3379,3381,3382,3405,3417,3418,3420,3433,3436,3448,3475,3477,3478,3493,3505,3506,3508,3529,3532,3544,3560,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 75,1,1⟩,⟨.covers 139,1,2⟩,⟨.covers 83,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 1539,1,2⟩,⟨.covers 78,1,2⟩,⟨.covers 142,1,2⟩,⟨.covers 198,1,2⟩,⟨.covers 3078,1,1⟩,⟨.covers 202,1,2⟩,⟨.covers 3082,1,1⟩,⟨.covers 114,1,2⟩,⟨.covers 178,1,1⟩,⟨.covers 2818,1,2⟩,⟨.covers 3330,1,1⟩,⟨.covers 3586,1,1⟩,⟨.covers 864,1,2⟩,⟨.incident 1,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_001
namespace C13.Global.FastDual17_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,10]
def points : Finset C13.Point := {1,3,6,10}
def columns : List Code := [701,743,829,949,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1766,1882,1894,1906,1945,1957,1969,2231,2285,2413,2425,2455,2483,2485,2486,2537,2677,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2773,2789,2861,2869,2873,2876,2901,2917,2921,2929,2951,2963,2965,2966,2979,2981,2982,2985,2986,2988,2993,2994,2996,3000,3011,3013,3025,3041,3127,3251,3253,3277,3292,3308,3379,3418,3493,3505,3532,3544,3623,3635,3686,3725,3737,3749,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 1031,1,9⟩,⟨.covers 75,1,6⟩,⟨.covers 139,1,11⟩,⟨.covers 1043,1,2⟩,⟨.covers 2307,1,6⟩,⟨.covers 1539,1,2⟩,⟨.covers 77,1,11⟩,⟨.covers 777,1,8⟩,⟨.covers 1289,1,3⟩,⟨.covers 78,1,7⟩,⟨.covers 142,1,11⟩,⟨.covers 86,1,4⟩,⟨.covers 198,1,11⟩,⟨.covers 154,1,6⟩,⟨.covers 106,1,11⟩,⟨.covers 202,1,3⟩,⟨.covers 1546,1,11⟩,⟨.covers 3082,1,11⟩,⟨.covers 178,1,6⟩,⟨.covers 2818,1,6⟩,⟨.covers 156,1,8⟩,⟨.covers 540,1,3⟩,⟨.covers 2324,1,6⟩,⟨.covers 1796,1,11⟩,⟨.covers 3332,1,4⟩,⟨.covers 216,1,3⟩,⟨.covers 2824,1,3⟩,⟨.covers 3592,1,11⟩,⟨.covers 2160,1,11⟩,⟨.covers 1200,1,4⟩,⟨.covers 1584,1,7⟩,⟨.covers 720,1,11⟩,⟨.covers 480,1,11⟩,⟨.covers 3168,1,11⟩,⟨.covers 3456,1,7⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_002
namespace C13.Global.FastDual17_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,11]
def points : Finset C13.Point := {1,3,6,11}
def columns : List Code := [701,743,829,949,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1724,1766,1821,1845,1849,1852,1863,1875,1878,1882,1891,1894,1906,1941,1945,1948,1957,1969,1972,1976,1987,1990,2002,2018,2231,2285,2413,2425,2455,2483,2486,2537,2677,2731,2734,2739,2742,2746,2773,2901,2921,2929,2966,2986,2994,3127,3251,3254,3277,3292,3308,3351,3379,3405,3433,3478,3506,3532,3560,3635,3669,3754,3762,3788,3796]
def rows : List LinearRow := [⟨.covers 75,1,2⟩,⟨.covers 139,1,1⟩,⟨.covers 201,1,2⟩,⟨.covers 777,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 78,1,2⟩,⟨.covers 142,1,2⟩,⟨.covers 202,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 2316,1,2⟩,⟨.covers 120,1,2⟩,⟨.covers 184,1,1⟩,⟨.covers 216,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 3592,1,2⟩,⟨.covers 3168,1,2⟩,⟨.incident 3,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_003
namespace C13.Global.FastDual17_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,8]
def points : Finset C13.Point := {1,3,7,8}
def columns : List Code := [381,471,829,889,892,967,979,995,1143,1245,1371,1374,1401,1402,1404,1461,1509,1639,1651,1653,1654,1693,1721,1753,1852,1882,1912,1957,1987,2017,2413,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2861,2876,2921,2936,2951,2966,3011,3026,3127,3187,3189,3190,3277,3292,3308,3418,3433,3448,3478,3493,3508,3623,3635,3637,3638,3669,3683,3685,3686,3697,3698,3700,3725,3737,3740,3753,3754,3756,3768,3785,3788,3800,3816,3854,3884,3914,3944,3974,4004,4034,4064]
def rows : List LinearRow := [⟨.covers 1031,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 139,1,2⟩,⟨.covers 1283,1,1⟩,⟨.covers 2307,1,2⟩,⟨.covers 1539,1,1⟩,⟨.covers 78,1,2⟩,⟨.covers 142,1,2⟩,⟨.covers 198,1,2⟩,⟨.covers 106,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 178,1,2⟩,⟨.covers 3090,1,1⟩,⟨.covers 226,1,1⟩,⟨.covers 912,1,2⟩,⟨.incident 1,8,-2⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_004
namespace C13.Global.FastDual17_005
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,9]
def points : Finset C13.Point := {1,3,7,9}
def columns : List Code := [381,471,829,885,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1653,1654,1693,1721,1753,1821,1852,1863,1877,1894,1908,1945,1987,2001,2413,2421,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2876,2901,2932,2986,3011,3042,3127,3187,3189,3190,3277,3292,3308,3351,3379,3381,3382,3405,3411,3413,3414,3417,3418,3420,3429,3433,3436,3441,3442,3444,3448,3477,3478,3493,3508,3525,3532,3540,3556,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 519,1,10⟩,⟨.covers 2055,1,4⟩,⟨.covers 75,1,12⟩,⟨.covers 139,1,1⟩,⟨.covers 147,1,7⟩,⟨.covers 99,1,1⟩,⟨.covers 141,1,7⟩,⟨.covers 2061,1,3⟩,⟨.covers 297,1,1⟩,⟨.covers 777,1,10⟩,⟨.covers 2569,1,10⟩,⟨.covers 3081,1,1⟩,⟨.covers 2097,1,3⟩,⟨.covers 417,1,4⟩,⟨.covers 2337,1,1⟩,⟨.covers 3105,1,1⟩,⟨.covers 2625,1,1⟩,⟨.covers 78,1,12⟩,⟨.covers 166,1,4⟩,⟨.covers 774,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 202,1,12⟩,⟨.covers 778,1,7⟩,⟨.covers 1546,1,12⟩,⟨.covers 114,1,6⟩,⟨.covers 210,1,4⟩,⟨.covers 3330,1,6⟩,⟨.covers 156,1,4⟩,⟨.covers 108,1,4⟩,⟨.covers 172,1,1⟩,⟨.covers 2316,1,1⟩,⟨.covers 2572,1,6⟩,⟨.covers 2820,1,4⟩,⟨.covers 3588,1,10⟩,⟨.covers 120,1,6⟩,⟨.covers 184,1,12⟩,⟨.covers 1800,1,1⟩,⟨.covers 3336,1,6⟩,⟨.covers 624,1,1⟩,⟨.covers 432,1,7⟩,⟨.covers 2256,1,7⟩,⟨.covers 480,1,1⟩,⟨.covers 1248,1,6⟩,⟨.covers 928,1,4⟩,⟨.covers 1824,1,10⟩,⟨.covers 1728,1,12⟩,⟨.covers 2880,1,6⟩,⟨.covers 3456,1,4⟩]
def bound : Int := 12

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_005
namespace C13.Global.FastDual17_006
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,10]
def points : Finset C13.Point := {1,3,7,10}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1371,1374,1395,1398,1402,1461,1509,1639,1651,1654,1693,1721,1753,1882,1894,1906,1945,1957,1969,2413,2421,2425,2428,2455,2486,2518,2677,2731,2734,2746,2794,2861,2869,2873,2876,2901,2917,2921,2924,2929,2932,2936,2951,2963,2966,2979,2982,2986,2994,3011,3014,3026,3042,3127,3187,3190,3277,3292,3308,3379,3418,3442,3493,3532,3556,3623,3635,3686,3698,3725,3737,3788,3800]
def rows : List LinearRow := [⟨.covers 75,1,1⟩,⟨.covers 139,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 778,1,1⟩,⟨.covers 108,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 3216,1,1⟩,⟨.incident 3,8,-1⟩]
def bound : Int := 0

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_006
namespace C13.Global.FastDual17_007
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,7,11]
def points : Finset C13.Point := {1,3,7,11}
def columns : List Code := [381,471,829,885,889,892,967,979,995,1143,1245,1367,1371,1373,1374,1395,1397,1398,1401,1402,1404,1461,1493,1509,1639,1651,1653,1654,1693,1721,1753,1821,1845,1849,1852,1863,1875,1877,1878,1881,1882,1884,1891,1893,1894,1905,1906,1908,1912,1941,1945,1957,1969,1987,1989,2001,2017,2413,2421,2425,2455,2486,2518,2677,2731,2734,2746,2794,2901,2921,2929,2966,2986,2994,3127,3187,3189,3277,3292,3308,3351,3379,3405,3413,3433,3441,3478,3532,3540,3635,3669,3697,3754,3788,3816]
def rows : List LinearRow := [⟨.covers 135,1,1⟩,⟨.covers 75,1,1⟩,⟨.covers 2307,1,1⟩,⟨.covers 1539,1,1⟩,⟨.covers 2563,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 777,1,1⟩,⟨.covers 2569,1,1⟩,⟨.covers 3081,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 1062,1,1⟩,⟨.covers 198,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 2314,1,1⟩,⟨.covers 3082,1,1⟩,⟨.covers 114,1,1⟩,⟨.covers 178,1,1⟩,⟨.covers 1794,1,1⟩,⟨.covers 156,1,1⟩,⟨.covers 172,1,1⟩,⟨.covers 300,1,1⟩,⟨.covers 2820,1,1⟩,⟨.covers 3588,1,1⟩,⟨.covers 120,1,1⟩,⟨.covers 1800,1,1⟩,⟨.covers 2160,1,1⟩,⟨.covers 1200,1,1⟩,⟨.covers 720,1,1⟩,⟨.covers 480,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 2496,1,1⟩,⟨.covers 3648,1,1⟩,⟨.covers 3456,1,1⟩]
def bound : Int := 2

theorem column_mask : listMask columns = restrictMask universeMask Source17.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source17.rootCodes link17 points rows bound = true := by decide +kernel

end C13.Global.FastDual17_007
