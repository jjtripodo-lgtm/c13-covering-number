import C13Global.BasicData
import C13Enumeration.Census.BlockUniverse
namespace C13.Global
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def quadCodes : List Code := [15,23,39,71,135,263,519,1031,2055,27,43,75,139,267,523,1035,2059,51,83,147,275,531,1043,2067,99,163,291,547,1059,2083,195,323,579,1091,2115,387,643,1155,2179,771,1283,2307,1539,2563,3075,29,45,77,141,269,525,1037,2061,53,85,149,277,533,1045,2069,101,165,293,549,1061,2085,197,325,581,1093,2117,389,645,1157,2181,773,1285,2309,1541,2565,3077,57,89,153,281,537,1049,2073,105,169,297,553,1065,2089,201,329,585,1097,2121,393,649,1161,2185,777,1289,2313,1545,2569,3081,113,177,305,561,1073,2097,209,337,593,1105,2129,401,657,1169,2193,785,1297,2321,1553,2577,3089,225,353,609,1121,2145,417,673,1185,2209,801,1313,2337,1569,2593,3105,449,705,1217,2241,833,1345,2369,1601,2625,3137,897,1409,2433,1665,2689,3201,1793,2817,3329,3585,30,46,78,142,270,526,1038,2062,54,86,150,278,534,1046,2070,102,166,294,550,1062,2086,198,326,582,1094,2118,390,646,1158,2182,774,1286,2310,1542,2566,3078,58,90,154,282,538,1050,2074,106,170,298,554,1066,2090,202,330,586,1098,2122,394,650,1162,2186,778,1290,2314,1546,2570,3082,114,178,306,562,1074,2098,210,338,594,1106,2130,402,658,1170,2194,786,1298,2322,1554,2578,3090,226,354,610,1122,2146,418,674,1186,2210,802,1314,2338,1570,2594,3106,450,706,1218,2242,834,1346,2370,1602,2626,3138,898,1410,2434,1666,2690,3202,1794,2818,3330,3586,60,92,156,284,540,1052,2076,108,172,300,556,1068,2092,204,332,588,1100,2124,396,652,1164,2188,780,1292,2316,1548,2572,3084,116,180,308,564,1076,2100,212,340,596,1108,2132,404,660,1172,2196,788,1300,2324,1556,2580,3092,228,356,612,1124,2148,420,676,1188,2212,804,1316,2340,1572,2596,3108,452,708,1220,2244,836,1348,2372,1604,2628,3140,900,1412,2436,1668,2692,3204,1796,2820,3332,3588,120,184,312,568,1080,2104,216,344,600,1112,2136,408,664,1176,2200,792,1304,2328,1560,2584,3096,232,360,616,1128,2152,424,680,1192,2216,808,1320,2344,1576,2600,3112,456,712,1224,2248,840,1352,2376,1608,2632,3144,904,1416,2440,1672,2696,3208,1800,2824,3336,3592,240,368,624,1136,2160,432,688,1200,2224,816,1328,2352,1584,2608,3120,464,720,1232,2256,848,1360,2384,1616,2640,3152,912,1424,2448,1680,2704,3216,1808,2832,3344,3600,480,736,1248,2272,864,1376,2400,1632,2656,3168,928,1440,2464,1696,2720,3232,1824,2848,3360,3616,960,1472,2496,1728,2752,3264,1856,2880,3392,3648,1920,2944,3456,3712,3840]
theorem quadCodes_chain : quadCodes.IsChain (fun a b => b.reverse.toNat < a.reverse.toNat) := by decide +kernel

theorem quadCodes_card : quadCodes.toFinset.card = 495 := by
  have hp : quadCodes.Pairwise (fun a b => b.reverse.toNat < a.reverse.toNat) :=
    List.isChain_iff_pairwise.mp quadCodes_chain
  have hn : quadCodes.Nodup := hp.imp (by intro a b h he; subst b; exact Nat.lt_irrefl _ h)
  rw [List.toFinset_card_of_nodup hn]
  decide

def validQuadB (b : Code) : Bool := decide (decodeTyped b ⊆ univ.erase hole ∧ (decodeTyped b).card = 4)
theorem quadValid00 : ((quadCodes.drop 0).take 33).all validQuadB = true := by decide +kernel
theorem quadValid01 : ((quadCodes.drop 33).take 33).all validQuadB = true := by decide +kernel
theorem quadValid02 : ((quadCodes.drop 66).take 33).all validQuadB = true := by decide +kernel
theorem quadValid03 : ((quadCodes.drop 99).take 33).all validQuadB = true := by decide +kernel
theorem quadValid04 : ((quadCodes.drop 132).take 33).all validQuadB = true := by decide +kernel
theorem quadValid05 : ((quadCodes.drop 165).take 33).all validQuadB = true := by decide +kernel
theorem quadValid06 : ((quadCodes.drop 198).take 33).all validQuadB = true := by decide +kernel
theorem quadValid07 : ((quadCodes.drop 231).take 33).all validQuadB = true := by decide +kernel
theorem quadValid08 : ((quadCodes.drop 264).take 33).all validQuadB = true := by decide +kernel
theorem quadValid09 : ((quadCodes.drop 297).take 33).all validQuadB = true := by decide +kernel
theorem quadValid10 : ((quadCodes.drop 330).take 33).all validQuadB = true := by decide +kernel
theorem quadValid11 : ((quadCodes.drop 363).take 33).all validQuadB = true := by decide +kernel
theorem quadValid12 : ((quadCodes.drop 396).take 33).all validQuadB = true := by decide +kernel
theorem quadValid13 : ((quadCodes.drop 429).take 33).all validQuadB = true := by decide +kernel
theorem quadValid14 : ((quadCodes.drop 462).take 33).all validQuadB = true := by decide +kernel
theorem quadCodes_valid : quadCodes.all validQuadB = true := by
  have he : quadCodes = ((quadCodes.drop 0).take 33) ++ ((quadCodes.drop 33).take 33) ++ ((quadCodes.drop 66).take 33) ++ ((quadCodes.drop 99).take 33) ++ ((quadCodes.drop 132).take 33) ++ ((quadCodes.drop 165).take 33) ++ ((quadCodes.drop 198).take 33) ++ ((quadCodes.drop 231).take 33) ++ ((quadCodes.drop 264).take 33) ++ ((quadCodes.drop 297).take 33) ++ ((quadCodes.drop 330).take 33) ++ ((quadCodes.drop 363).take 33) ++ ((quadCodes.drop 396).take 33) ++ ((quadCodes.drop 429).take 33) ++ ((quadCodes.drop 462).take 33) := by decide +kernel
  rw [he]
  simp only [List.all_append,Bool.and_eq_true,and_assoc]
  exact ⟨quadValid00,quadValid01,quadValid02,quadValid03,quadValid04,quadValid05,quadValid06,quadValid07,quadValid08,quadValid09,quadValid10,quadValid11,quadValid12,quadValid13,quadValid14⟩

theorem quadCodes_complete : (quadCodes.map decodeTyped).toFinset =
    (univ.erase hole).powersetCard 4 := by
  have hsub : (quadCodes.map decodeTyped).toFinset ⊆ (univ.erase hole).powersetCard 4 := by
    intro B hB
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hB)
    exact mem_powersetCard.mpr (of_decide_eq_true (List.all_eq_true.mp quadCodes_valid c hc))
  apply Finset.eq_of_subset_of_card_le hsub
  have hc : (quadCodes.map decodeTyped).toFinset.card = 495 := by
    rw [list_map_finset,card_image_of_injective _ decodeTyped_injective]
    exact quadCodes_card
  rw [hc,card_powersetCard]
  simp only [card_erase_of_mem (mem_univ hole),card_univ,Fintype.card_fin]
  decide
end C13.Global
