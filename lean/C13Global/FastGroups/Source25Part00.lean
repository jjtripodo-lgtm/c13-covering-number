import C13Global.DirectDual
import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source25
namespace C13.Global.FastDual25_000
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,9]
def points : Finset C13.Point := {1,3,6,9}
def columns : List Code := [701,743,829,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1721,1724,1766,1821,1852,1863,1894,1945,1976,1987,2018,2231,2285,2413,2425,2455,2483,2485,2486,2537,2677,2731,2734,2745,2746,2748,2773,2876,2901,2986,3000,3011,3025,3127,3251,3253,3254,3277,3292,3308,3351,3379,3381,3382,3405,3417,3418,3420,3433,3436,3448,3475,3477,3478,3493,3505,3506,3508,3529,3532,3544,3560,3669,3686,3700,3737,3754,3768]
def rows : List LinearRow := [⟨.covers 2055,1,2⟩,⟨.covers 75,1,15⟩,⟨.covers 139,1,10⟩,⟨.covers 147,1,1⟩,⟨.covers 2307,1,2⟩,⟨.covers 1539,1,12⟩,⟨.covers 525,1,1⟩,⟨.covers 297,1,3⟩,⟨.covers 201,1,2⟩,⟨.covers 1161,1,3⟩,⟨.covers 777,1,2⟩,⟨.covers 3081,1,6⟩,⟨.covers 113,1,11⟩,⟨.covers 1073,1,2⟩,⟨.covers 1313,1,2⟩,⟨.covers 78,1,15⟩,⟨.covers 142,1,10⟩,⟨.covers 198,1,12⟩,⟨.covers 3078,1,3⟩,⟨.covers 154,1,2⟩,⟨.covers 106,1,15⟩,⟨.covers 202,1,3⟩,⟨.covers 778,1,10⟩,⟨.covers 3082,1,10⟩,⟨.covers 178,1,4⟩,⟨.covers 210,1,10⟩,⟨.covers 3330,1,1⟩,⟨.covers 108,1,3⟩,⟨.covers 300,1,2⟩,⟨.covers 1164,1,3⟩,⟨.covers 2316,1,6⟩,⟨.covers 1548,1,2⟩,⟨.covers 308,1,1⟩,⟨.covers 212,1,11⟩,⟨.covers 404,1,1⟩,⟨.covers 2436,1,1⟩,⟨.covers 184,1,4⟩,⟨.covers 232,1,9⟩,⟨.covers 1800,1,5⟩,⟨.covers 3336,1,2⟩,⟨.covers 848,1,1⟩,⟨.covers 1616,1,2⟩,⟨.covers 864,1,12⟩,⟨.covers 3360,1,1⟩,⟨.covers 2880,1,11⟩,⟨.covers 3648,1,9⟩,⟨.covers 3456,1,1⟩,⟨.incident 1,8,-1⟩,⟨.incident 3,8,-3⟩,⟨.incident 6,8,-5⟩]
def bound : Int := 7

theorem column_mask : listMask columns = restrictMask universeMask Source25.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source25.rootCodes link25 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual25_000
namespace C13.Global.FastDual25_001
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [1,3,6,10]
def points : Finset C13.Point := {1,3,6,10}
def columns : List Code := [701,743,829,949,953,956,967,979,995,1371,1374,1402,1461,1498,1639,1654,1693,1717,1721,1766,1882,1894,1906,1945,1957,1969,2231,2285,2413,2425,2455,2483,2485,2486,2537,2677,2727,2731,2733,2734,2739,2741,2742,2745,2746,2748,2773,2789,2861,2869,2873,2876,2901,2917,2921,2929,2951,2963,2965,2966,2979,2981,2982,2985,2986,2988,2993,2994,2996,3000,3011,3013,3025,3041,3127,3251,3253,3277,3292,3308,3379,3418,3493,3505,3532,3544,3623,3635,3686,3725,3737,3749,3761,3788,3812]
def rows : List LinearRow := [⟨.covers 139,1,1⟩,⟨.covers 147,1,1⟩,⟨.covers 99,1,1⟩,⟨.covers 269,1,1⟩,⟨.covers 89,1,1⟩,⟨.covers 201,1,1⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,1⟩,⟨.covers 3078,1,1⟩,⟨.covers 106,1,1⟩,⟨.covers 202,1,1⟩,⟨.covers 1546,1,1⟩,⟨.covers 1548,1,1⟩,⟨.covers 116,1,1⟩,⟨.covers 212,1,1⟩,⟨.covers 184,1,1⟩,⟨.covers 3336,1,1⟩,⟨.covers 3600,1,1⟩,⟨.covers 1248,1,1⟩,⟨.covers 3360,1,1⟩,⟨.covers 2880,1,1⟩,⟨.covers 1920,1,1⟩]
def bound : Int := 1

theorem column_mask : listMask columns = restrictMask universeMask Source25.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source25.rootCodes link25 points rows bound = true := by
  apply directLeafCheck_sound
  decide +kernel

end C13.Global.FastDual25_001
