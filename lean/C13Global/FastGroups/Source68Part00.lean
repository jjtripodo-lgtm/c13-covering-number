import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source68
namespace C13.Global.FastDual68_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,1,2,3]
def points : Finset C13.Point := {0,1,2,3}
def columns : List Code := [758,886,926,942,950,982,998,1016,1269,1373,1389,1397,1461,1493,1509,1528,1654,1717,1747,1749,1750,1763,1765,1766,1819,1835,1843,1875,1877,1878,1891,1893,1894,1912,1939,1941,1942,1955,1957,1958,1976,2008,2024,2032,2267,2283,2291,2419,2483,2515,2531,2552,2678,2717,2733,2741,2771,2773,2774,2787,2789,2790,2808,2867,2899,2901,2902,2915,2917,2918,2963,2965,2966,2979,2981,2982,3000,3032,3048,3056,3166,3182,3190,3253,3283,3285,3286,3299,3301,3302,3320,3379,3411,3413,3414,3427,3429,3430,3448,3475,3477,3478,3491,3493,3494,3544,3560,3568,3670,3686,3704,3733,3749,3768,3800,3816,3824,3859,3875,3896,3928,3944,3952,3992,4008,4016,4048,4064]
def rows : List LinearRow := [⟨.covers 579,1,1⟩,⟨.covers 1155,1,1⟩,⟨.covers 1157,1,1⟩,⟨.covers 2309,1,1⟩,⟨.covers 1158,1,1⟩,⟨.covers 2322,1,1⟩,⟨.covers 2338,1,1⟩,⟨.covers 596,1,1⟩,⟨.covers 612,1,1⟩,⟨.covers 456,1,3⟩,⟨.covers 3592,1,3⟩,⟨.covers 464,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 480,1,1⟩,⟨.covers 3616,1,1⟩,⟨.covers 2752,1,1⟩,⟨.covers 3264,1,1⟩,⟨.covers 1856,1,1⟩,⟨.covers 3392,1,1⟩,⟨.covers 1920,1,1⟩,⟨.covers 2944,1,1⟩,⟨.incident 0,8,3⟩,⟨.incident 1,8,3⟩,⟨.incident 2,8,3⟩,⟨.incident 3,8,2⟩]
def bound : Int := 8

theorem column_mask : listMask columns = restrictMask universeMask Source68.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source68.rootCodes figure6 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual68_000
namespace C13.Global.FastDual68_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,1,2,6]
def points : Finset C13.Point := {0,1,2,6}
def columns : List Code := [638,734,750,758,862,878,886,926,942,950,982,998,1016,1213,1373,1389,1437,1453,1461,1528,1630,1646,1654,1693,1709,1717,1747,1750,1763,1766,1819,1835,1843,1877,1878,1893,1894,1939,1941,1942,1955,1957,1958,1976,2008,2024,2032,2267,2283,2363,2459,2475,2483,2552,2654,2670,2678,2717,2733,2741,2771,2774,2787,2790,2843,2859,2867,2901,2902,2917,2918,2963,2965,2966,2979,2981,2982,3000,3032,3048,3056,3166,3182,3229,3245,3253,3355,3371,3379,3470,3475,3477,3478,3491,3493,3494,3512,3544,3560,3670,3686,3733,3749,3768,3859,3875,3896,3992,4008,4016,4048,4064]
def rows : List LinearRow := [⟨.covers 75,1,2⟩,⟨.covers 1091,1,2⟩,⟨.covers 2307,1,1⟩,⟨.covers 1157,1,1⟩,⟨.covers 1158,1,1⟩,⟨.covers 1098,1,1⟩,⟨.covers 650,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 332,1,2⟩,⟨.covers 2124,1,1⟩,⟨.covers 2572,1,1⟩,⟨.covers 2372,1,2⟩,⟨.covers 456,1,6⟩,⟨.covers 3592,1,9⟩,⟨.covers 464,1,2⟩,⟨.covers 480,1,2⟩,⟨.covers 2752,1,2⟩,⟨.covers 3264,1,2⟩,⟨.covers 1856,1,2⟩,⟨.covers 3648,1,2⟩,⟨.incident 0,8,4⟩,⟨.incident 1,8,4⟩,⟨.incident 2,8,4⟩,⟨.incident 6,8,-1⟩]
def bound : Int := 9

theorem column_mask : listMask columns = restrictMask universeMask Source68.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source68.rootCodes figure6 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual68_001
namespace C13.Global.FastDual68_002
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,1,3,6]
def points : Finset C13.Point := {0,1,3,6}
def columns : List Code := [508,758,886,926,942,950,956,982,988,998,1004,1012,1016,1373,1389,1404,1461,1500,1516,1528,1654,1717,1747,1750,1763,1766,1815,1819,1821,1822,1831,1835,1837,1838,1843,1845,1846,1852,1877,1878,1884,1893,1894,1900,1908,1939,1941,1942,1948,1955,1957,1958,1964,1972,1976,2004,2008,2020,2024,2032,2267,2270,2283,2286,2359,2455,2471,2483,2485,2486,2524,2540,2552,2678,2717,2733,2741,2748,2771,2774,2787,2790,2839,2855,2867,2869,2870,2901,2902,2917,2918,2932,2963,2965,2966,2972,2979,2981,2982,2988,2996,3000,3028,3032,3044,3048,3056,3166,3182,3253,3351,3367,3379,3381,3382,3420,3436,3475,3477,3478,3491,3493,3494,3508,3544,3560,3644,3670,3686,3733,3740,3749,3756,3764,3768,3859,3861,3862,3868,3875,3877,3878,3884,3892,3896,3924,3940,3988,3992,4004,4008,4016,4048,4064]
def rows : List LinearRow := [⟨.covers 2307,1,67⟩,⟨.covers 141,1,133⟩,⟨.covers 1157,1,133⟩,⟨.covers 777,1,133⟩,⟨.covers 270,1,133⟩,⟨.covers 1158,1,33⟩,⟨.covers 2182,1,33⟩,⟨.covers 1286,1,33⟩,⟨.covers 1098,1,33⟩,⟨.covers 2322,1,33⟩,⟨.covers 2338,1,33⟩,⟨.covers 898,1,33⟩,⟨.covers 3202,1,33⟩,⟨.covers 456,1,33⟩,⟨.covers 3592,1,167⟩,⟨.covers 3648,1,33⟩,⟨.incident 0,8,33⟩,⟨.incident 6,8,133⟩]
def bound : Int := 167

theorem column_mask : listMask columns = restrictMask universeMask Source68.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source68.rootCodes figure6 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual68_002
namespace C13.Global.FastDual68_003
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,1,3,8]
def points : Finset C13.Point := {0,1,3,8}
def columns : List Code := [508,758,926,942,988,1004,1016,1269,1373,1389,1500,1516,1528,1654,1717,1747,1749,1750,1763,1765,1766,1780,1819,1835,2008,2024,2263,2267,2269,2270,2279,2283,2285,2286,2291,2293,2294,2300,2359,2391,2407,2419,2421,2455,2471,2483,2486,2515,2517,2518,2524,2531,2533,2534,2540,2548,2552,2678,2717,2733,2741,2748,2771,2773,2774,2780,2787,2789,2790,2796,2804,2808,2839,2855,2867,2899,2901,2915,2917,2963,2966,2979,2982,3028,3032,3044,3048,3056,3166,3182,3190,3196,3253,3283,3285,3286,3292,3299,3301,3302,3308,3316,3320,3351,3367,3379,3411,3413,3427,3429,3475,3478,3491,3494,3540,3544,3556,3560,3568,3644,3670,3676,3686,3692,3700,3704,3733,3740,3749,3756,3764,3768,3796,3800,3812,3816,3824,3859,3875,4036,4048,4064]
def rows : List LinearRow := [⟨.covers 75,1,10⟩,⟨.covers 579,1,3⟩,⟨.covers 1091,1,3⟩,⟨.covers 643,1,3⟩,⟨.covers 1155,1,3⟩,⟨.covers 141,1,10⟩,⟨.covers 1157,1,13⟩,⟨.covers 773,1,3⟩,⟨.covers 78,1,10⟩,⟨.covers 582,1,13⟩,⟨.covers 1286,1,3⟩,⟨.covers 3592,1,10⟩,⟨.covers 3840,1,3⟩,⟨.incident 3,8,3⟩,⟨.incident 8,8,10⟩]
def bound : Int := 13

theorem column_mask : listMask columns = restrictMask universeMask Source68.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source68.rootCodes figure6 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual68_003
namespace C13.Global.FastDual68_004
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [0,1,6,7]
def points : Finset C13.Point := {0,1,6,7}
def columns : List Code := [508,638,830,862,878,886,892,926,942,956,988,1004,1016,1213,1341,1373,1389,1404,1437,1453,1461,1468,1500,1516,1528,1630,1646,1654,1693,1709,1717,1747,1763,1815,1819,1821,1822,1831,1835,1837,1838,1843,1845,1846,1852,1877,1878,1884,1893,1894,1900,1908,1941,1942,1948,1957,1958,1964,1972,2004,2008,2020,2024,2032,2174,2237,2267,2283,2335,2351,2359,2363,2365,2366,2397,2398,2413,2414,2428,2461,2462,2477,2478,2492,2524,2540,2552,2654,2670,2678,2717,2733,2839,2843,2845,2846,2855,2859,2861,2862,2867,2869,2870,2876,2901,2902,2908,2917,2918,2924,2932,2972,2988,3032,3048,3166,3182,3229,3245,3253,3351,3355,3357,3358,3367,3371,3373,3374,3379,3381,3382,3388,3420,3436,3477,3478,3484,3493,3494,3500,3508,3544,3560,3644,3670,3686,3733,3749,3859,3861,3862,3868,3875,3877,3878,3884,3892,3896,3924,3940,3988,4004,4048,4064]
def rows : List LinearRow := [⟨.covers 523,1,5⟩,⟨.covers 1035,1,5⟩,⟨.covers 275,1,5⟩,⟨.covers 291,1,5⟩,⟨.covers 2307,1,10⟩,⟨.covers 525,1,1⟩,⟨.covers 2061,1,1⟩,⟨.covers 149,1,1⟩,⟨.covers 165,1,1⟩,⟨.covers 2117,1,15⟩,⟨.covers 1157,1,2⟩,⟨.covers 1097,1,16⟩,⟨.covers 2625,1,1⟩,⟨.covers 2689,1,1⟩,⟨.covers 1793,1,1⟩,⟨.covers 1038,1,4⟩,⟨.covers 2062,1,4⟩,⟨.covers 86,1,4⟩,⟨.covers 102,1,4⟩,⟨.covers 582,1,8⟩,⟨.covers 650,1,4⟩,⟨.covers 3202,1,4⟩,⟨.covers 1794,1,4⟩,⟨.covers 3140,1,4⟩,⟨.covers 3592,1,20⟩,⟨.incident 6,8,4⟩,⟨.incident 7,8,16⟩]
def bound : Int := 20

theorem column_mask : listMask columns = restrictMask universeMask Source68.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source68.rootCodes figure6 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual68_004
