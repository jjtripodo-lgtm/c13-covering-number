import C13Global.CensusCore
namespace C13.Global
open Finset C13.SourceData
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Precisely the actual-cover obstruction required at every catalog root and
four-element set. No Boolean abstract-join assertion is hidden in this interface. -/
def CatalogObstructions : Prop :=
  ∀ K ∈ catalog, ∀ Q ∈ (univ.erase hole).powersetCard 4, ActualObstruction K Q

/-- The global normalization and degree-counting argument, with its semantic
finite-census interface explicit. This lemma does not assert that interface. -/
theorem no_cover29_of_catalog (hcensus : CatalogObstructions)
    (hminimum : PublishedMinimumBound Point)
    (hpublished : PublishedClassification1995)
    (F : Family Point) (hcover : IsCoverOn univ F 7 4) : F.card ≠ 29 := by
  intro h29
  have hclass : ClassifiesMinimumLinks catalog hole :=
    classification_of_source_coverage rawSources catalog hole hpublished
      C13.OrbitPilot.AllSources.catalog_covers_all_raw_sources
  obtain ⟨K,G,hK,hG,hG29,hroot,hdroot⟩ :=
    normalize_cover29 catalog hole hminimum hclass F hcover h29
  have hd := all_degrees_ge15 G hG hminimum
  have hs : ∑ q : Point, degree G q = 203 := by
    rw [sum_degrees_uniform G 7 (fun B hB => (hG.1 B hB).2),hG29]
  have hf := five_minimum_degrees (degree G) hd hs
  let M := univ.filter (degree G · = 15)
  have hm : hole ∈ M := mem_filter.mpr ⟨mem_univ _,hdroot⟩
  have hfm : 5 ≤ M.card := hf
  have he : 4 ≤ (M.erase hole).card := by rw [card_erase_of_mem hm]; omega
  obtain ⟨Q,hQM,hQ⟩ := exists_subset_card_eq he
  have hQuniv : Q ⊆ univ.erase hole := by
    intro q hq
    exact mem_erase.mpr ⟨(mem_erase.mp (hQM hq)).1,mem_univ _⟩
  apply hcensus K hK Q (mem_powersetCard.mpr ⟨hQuniv,hQ⟩)
    hclass G hG hroot
  · intro q hq
    exact (mem_filter.mp (mem_erase.mp (hQM hq)).2).2
  · have hc := degree_add_outside G hole
    omega

theorem exact30_of_catalog (hcensus : CatalogObstructions)
    (hminimum : PublishedMinimumBound Point)
    (hpublished : PublishedClassification1995) :
    (∃ F : Family Point, IsCoverOn univ F 7 4 ∧ F.card = 30) ∧
    (∀ F : Family Point, IsCoverOn univ F 7 4 → 30 ≤ F.card) := by
  refine ⟨exists_cover30,?_⟩
  intro F hF
  by_contra h
  have hs : F.card ≤ 29 := by omega
  obtain ⟨G,hG,_,h29⟩ := pad_cover_to29 F hF hs
  exact no_cover29_of_catalog hcensus hminimum hpublished G hG h29

end C13.Global
