import C13Enumeration.Census.BlockValid00
import C13Enumeration.Census.BlockValid01
import C13Enumeration.Census.BlockValid02
import C13Enumeration.Census.BlockValid03
import C13Enumeration.Census.BlockValid04
import C13Enumeration.Census.BlockValid05
import C13Enumeration.Census.BlockValid06
import C13Enumeration.Census.BlockValid07
import C13Enumeration.Census.BlockValid08
namespace C13.Enumeration.Census
open Finset C13.Checker.RawSupport C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
theorem blockCodes_valid_checked : blockCodes.all validBlockB = true := by
  have hs : blockCodes = ((blockCodes.drop 0).take 32) ++ ((blockCodes.drop 32).take 32) ++ ((blockCodes.drop 64).take 32) ++ ((blockCodes.drop 96).take 32) ++ ((blockCodes.drop 128).take 32) ++ ((blockCodes.drop 160).take 32) ++ ((blockCodes.drop 192).take 32) ++ ((blockCodes.drop 224).take 32) ++ ((blockCodes.drop 256).take 32) ++ ((blockCodes.drop 288).take 32) ++ ((blockCodes.drop 320).take 32) ++ ((blockCodes.drop 352).take 32) ++ ((blockCodes.drop 384).take 32) ++ ((blockCodes.drop 416).take 32) ++ ((blockCodes.drop 448).take 32) ++ ((blockCodes.drop 480).take 32) ++ ((blockCodes.drop 512).take 32) ++ ((blockCodes.drop 544).take 32) ++ ((blockCodes.drop 576).take 32) ++ ((blockCodes.drop 608).take 32) ++ ((blockCodes.drop 640).take 32) ++ ((blockCodes.drop 672).take 32) ++ ((blockCodes.drop 704).take 32) ++ ((blockCodes.drop 736).take 32) ++ ((blockCodes.drop 768).take 32) := by decide +kernel
  rw [hs]
  simp only [List.all_append,Bool.and_eq_true,and_assoc]
  exact ⟨blockValid00,blockValid01,blockValid02,blockValid03,blockValid04,blockValid05,blockValid06,blockValid07,blockValid08,blockValid09,blockValid10,blockValid11,blockValid12,blockValid13,blockValid14,blockValid15,blockValid16,blockValid17,blockValid18,blockValid19,blockValid20,blockValid21,blockValid22,blockValid23,blockValid24⟩
theorem blockCodes_complete : decodeSource blockCodes =
    (Finset.univ.erase hole).powersetCard 7 := by
  have hsub : decodeSource blockCodes ⊆ (Finset.univ.erase hole).powersetCard 7 := by
    intro B hB
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hB)
    exact mem_powersetCard.mpr (of_decide_eq_true
      ((List.all_eq_true.mp blockCodes_valid_checked) c hc))
  apply Finset.eq_of_subset_of_card_le hsub
  have hc : (decodeSource blockCodes).card = 792 := by
    rw [decodeSource,list_map_finset,card_image_of_injective _ decodeTyped_injective]
    exact blockCodes_card
  rw [hc,card_powersetCard]
  simp only [card_erase_of_mem (mem_univ hole),card_univ,Fintype.card_fin]
  decide

theorem encode_mem_blockCodes (B : Finset Point) (hB : B ⊆ Finset.univ.erase hole)
    (hcard : B.card = 7) : encodeTyped B ∈ blockCodes := by
  have hb : B ∈ decodeSource blockCodes := by
    rw [blockCodes_complete]
    exact mem_powersetCard.mpr ⟨hB,hcard⟩
  obtain ⟨c,hc,hcB⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
  have he : encodeTyped B = c := by rw [← hcB,encode_decodeTyped]
  exact he.symm ▸ hc
end C13.Enumeration.Census
