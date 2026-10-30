import C13Covering.CatalogReduction

namespace C13
open Finset
variable {V : Type*} [DecidableEq V]

theorem transport_trans (e f : Equiv.Perm V) (F : Family V) :
    transport f (transport e F) = transport (e.trans f) F := by
  simp only [transport,image_image]
  apply image_congr
  intro B _
  exact map_map e.toEmbedding f.toEmbedding B

/-- Every literal classified source, including the exceptional Figure 6,
occurs in the catalog up to an isomorphism fixing the omitted thirteenth point.
Proving this for the 21,952 Figure-1 completions plus Figure 6 is an internal
finite task, separate from assuming the published classification theorem. -/
def CatalogCoversSources (sources catalog : Finset (Family V)) (hole : V) : Prop :=
  ∀ S ∈ sources, ∃ K ∈ catalog, ∃ e : Equiv.Perm V, e hole = hole ∧ transport e K = S

theorem classification_of_source_coverage [Fintype V]
    (sources catalog : Finset (Family V)) (hole : V)
    (hpublished : ClassifiesMinimumLinks sources hole)
    (hcoverage : CatalogCoversSources sources catalog hole) :
    ClassifiesMinimumLinks catalog hole := by
  intro q L hL hcard
  obtain ⟨S,hS,e,he,hSL⟩ := hpublished q L hL hcard
  obtain ⟨K,hK,f,hf,hKS⟩ := hcoverage S hS
  refine ⟨K,hK,f.trans e,?_,?_⟩
  · change e (f hole) = q
    rw [hf,he]
  · rw [← transport_trans,hKS,hSL]

/-- Keep the exceptional source explicit when proving family coverage. -/
theorem cover_sources_with_exception (ordinary catalog : Finset (Family V))
    (exceptional : Family V) (hole : V)
    (hordinary : CatalogCoversSources ordinary catalog hole)
    (hexceptional : exceptional ∈ catalog) :
    CatalogCoversSources (insert exceptional ordinary) catalog hole := by
  intro S hS
  rcases mem_insert.mp hS with h | h
  · subst S
    refine ⟨exceptional,hexceptional,Equiv.refl V,rfl,?_⟩
    unfold transport
    calc
      _ = exceptional.image id := by
        apply image_congr
        intro B _
        ext x
        simp
      _ = exceptional := image_id
  · exact hordinary S h

omit [DecidableEq V] in
theorem IsCoverOn.mono_family {U : Finset V} {F G : Family V} {k t : ℕ}
    (h : IsCoverOn U F k t) (hFG : F ⊆ G)
    (hblocks : ∀ B ∈ G, B ⊆ U ∧ B.card = k) : IsCoverOn U G k t := by
  refine ⟨hblocks,?_⟩
  intro T hTU hT
  obtain ⟨B,hB,hTB⟩ := h.2 T hTU hT
  exact ⟨B,hFG hB,hTB⟩

/-- Padding uses distinct unused seven-subsets, so no multiset or duplicate
block convention is smuggled into the simple-cover lower-bound reduction. -/
theorem pad_cover_to29 (F : Family Point) (hcover : IsCoverOn univ F 7 4)
    (hsize : F.card ≤ 29) :
    ∃ G : Family Point, IsCoverOn univ G 7 4 ∧ F ⊆ G ∧ G.card = 29 := by
  have hsub : F ⊆ univ.powersetCard 7 := by
    intro B hB
    exact mem_powersetCard.mpr (hcover.1 B hB)
  have hcapacity : 29 ≤ (univ.powersetCard 7 : Family Point).card := by
    rw [card_powersetCard,card_univ,Fintype.card_fin]
    decide
  obtain ⟨G,hFG,hGU,hG⟩ := exists_subsuperset_card_eq hsub hsize hcapacity
  refine ⟨G,hcover.mono_family hFG ?_,hFG,hG⟩
  intro B hB
  exact mem_powersetCard.mp (hGU hB)

theorem cover_card_ge30_of_catalog_obstruction
    (catalog : Finset (Family Point)) (hole : Point)
    (hpub : PublishedMinimumBound Point) (hclass : ClassifiesMinimumLinks catalog hole)
    (hfinite : CatalogObstruction catalog hole)
    (F : Family Point) (hcover : IsCoverOn univ F 7 4) : 30 ≤ F.card := by
  by_contra h
  have hsize : F.card ≤ 29 := by omega
  obtain ⟨G,hG,_,hG29⟩ := pad_cover_to29 F hcover hsize
  exact no_cover29_of_catalog_obstruction catalog hole hpub hclass hfinite G hG hG29

/-- Exact final lower-bound interface. The four premises are deliberately
separated: published minimum bound; published classification of the literal
source universe; internal catalog source coverage; and the all-class finite
pencil obstruction. This file proves the reduction, not the last two inputs. -/
theorem cover_card_ge30_from_source_and_obstruction
    (sources catalog : Finset (Family Point)) (hole : Point)
    (hminimum : PublishedMinimumBound Point)
    (hpublished : ClassifiesMinimumLinks sources hole)
    (hcoverage : CatalogCoversSources sources catalog hole)
    (hfinite : CatalogObstruction catalog hole)
    (F : Family Point) (hcover : IsCoverOn univ F 7 4) : 30 ≤ F.card :=
  cover_card_ge30_of_catalog_obstruction catalog hole hminimum
    (classification_of_source_coverage sources catalog hole hpublished hcoverage)
    hfinite F hcover

end C13
