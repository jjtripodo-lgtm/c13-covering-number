import C13Global.FastDual
import C13Global.FuelMask
import C13Global.Data.Source09
namespace C13.Global.FastDual09_016
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pointList : List Point := [6,8,9,11]
def points : Finset C13.Point := {6,8,9,11}
def columns : List Code := [127,191,223,239,254,319,351,367,379,415,431,439,445,446,463,475,491,506,575,607,623,631,671,687,699,701,702,719,727,743,758,799,815,829,830,847,911,956,967,971,979,995,1010,1087,1119,1135,1150,1183,1199,1207,1211,1213,1214,1231,1246,1262,1311,1327,1341,1342,1359,1371,1374,1387,1402,1423,1431,1438,1447,1453,1461,1462,1468,1483,1498,1567,1583,1597,1598,1615,1623,1639,1646,1654,1679,1691,1693,1707,1710,1721,1722,1724,1735,1766,1807,1852,1987,2111,2143,2159,2173,2207,2223,2231,2235,2238,2255,2269,2285,2300,2335,2351,2383,2411,2413,2425,2447,2455,2462,2486,2537,2552,2591,2607,2639,2647,2653,2677,2703,2731,2734,2746,2773,2804,2831,3056,3103,3119,3127,3131,3151,3165,3181,3215,3223,3230,3243,3246,3251,3254,3258,3277,3278,3292,3308,3343,3433,3478,3599,3669,3754]
def rows : List LinearRow := [⟨.covers 71,1,6⟩,⟨.covers 135,1,1⟩,⟨.covers 1031,1,3⟩,⟨.covers 75,1,6⟩,⟨.covers 139,1,1⟩,⟨.covers 1035,1,3⟩,⟨.covers 83,1,13⟩,⟨.covers 147,1,1⟩,⟨.covers 2067,1,12⟩,⟨.covers 99,1,13⟩,⟨.covers 163,1,1⟩,⟨.covers 2083,1,12⟩,⟨.covers 77,1,9⟩,⟨.covers 1037,1,1⟩,⟨.covers 149,1,4⟩,⟨.covers 101,1,4⟩,⟨.covers 293,1,18⟩,⟨.covers 197,1,9⟩,⟨.covers 389,1,16⟩,⟨.covers 89,1,4⟩,⟨.covers 537,1,18⟩,⟨.covers 169,1,4⟩,⟨.covers 201,1,9⟩,⟨.covers 649,1,16⟩,⟨.covers 2097,1,16⟩,⟨.covers 657,1,6⟩,⟨.covers 417,1,6⟩,⟨.covers 78,1,1⟩,⟨.covers 142,1,3⟩,⟨.covers 1038,1,24⟩,⟨.covers 550,1,17⟩,⟨.covers 282,1,17⟩,⟨.covers 1074,1,6⟩,⟨.covers 2098,1,17⟩,⟨.covers 210,1,11⟩,⟨.covers 1106,1,8⟩,⟨.covers 226,1,11⟩,⟨.covers 1122,1,8⟩,⟨.covers 2188,1,14⟩,⟨.covers 116,1,10⟩,⟨.covers 180,1,1⟩,⟨.covers 212,1,11⟩,⟨.covers 1124,1,12⟩,⟨.covers 420,1,17⟩,⟨.covers 1188,1,5⟩,⟨.covers 1220,1,9⟩,⟨.covers 2244,1,1⟩,⟨.covers 1796,1,5⟩,⟨.covers 2820,1,4⟩,⟨.covers 120,1,10⟩,⟨.covers 184,1,1⟩,⟨.covers 1112,1,12⟩,⟨.covers 664,1,17⟩,⟨.covers 1176,1,5⟩,⟨.covers 232,1,11⟩,⟨.covers 1224,1,9⟩,⟨.covers 2248,1,1⟩,⟨.covers 3592,1,4⟩,⟨.covers 1616,1,1⟩,⟨.covers 1808,1,31⟩,⟨.covers 3344,1,35⟩,⟨.covers 3600,1,30⟩,⟨.covers 3360,1,31⟩,⟨.covers 3616,1,31⟩,⟨.covers 1856,1,32⟩,⟨.incident 6,8,4⟩,⟨.incident 8,8,31⟩,⟨.incident 9,8,31⟩,⟨.incident 11,8,32⟩]
def bound : Int := 99

theorem column_mask : listMask columns = restrictMask universeMask Source09.alphabets pointList := by
  rw [← fuelListMask_eq]
  decide +kernel

theorem checked : fastLeafCheck columns Source09.rootCodes link09 points rows bound = true := by decide +kernel

end C13.Global.FastDual09_016
