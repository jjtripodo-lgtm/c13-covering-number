import C13Global.CatalogIrredundance
import C13Global.Census.Source01
import C13Global.Census.Source02
import C13Global.Census.Source03
import C13Global.Census.Source04
import C13Global.Census.Source05
import C13Global.Census.Source06
import C13Global.Census.Source07
import C13Global.Census.Source08
import C13Global.Census.Source09
import C13Global.Census.Source10
import C13Global.Census.Source11
import C13Global.Census.Source12
import C13Global.Census.Source13
import C13Global.Census.Source14
import C13Global.Census.Source15
import C13Global.Census.Source16
import C13Global.Census.Source17
import C13Global.Census.Source18
import C13Global.Census.Source19
import C13Global.Census.Source20
import C13Global.Census.Source21
import C13Global.Census.Source22
import C13Global.Census.Source23
import C13Global.Census.Source24
import C13Global.Census.Source25
import C13Global.Census.Source26
import C13Global.Census.Source27
import C13Global.Census.Source28
import C13Global.Census.Source29
import C13Global.Census.Source30
import C13Global.Census.Source31
import C13Global.Census.Source32
import C13Global.Census.Source33
import C13Global.Census.Source34
import C13Global.Census.Source35
import C13Global.Census.Source36
import C13Global.Census.Source37
import C13Global.Census.Source38
import C13Global.Census.Source39
import C13Global.Census.Source40
import C13Global.Census.Source41
import C13Global.Census.Source42
import C13Global.Census.Source43
import C13Global.Census.Source44
import C13Global.Census.Source45
import C13Global.Census.Source46
import C13Global.Census.Source47
import C13Global.Census.Source48
import C13Global.Census.Source49
import C13Global.Census.Source50
import C13Global.Census.Source51
import C13Global.Census.Source52
import C13Global.Census.Source53
import C13Global.Census.Source54
import C13Global.Census.Source55
import C13Global.Census.Source56
import C13Global.Census.Source57
import C13Global.Census.Source58
import C13Global.Census.Source59
import C13Global.Census.Source60
import C13Global.Census.Source61
import C13Global.Census.Source62
import C13Global.Census.Source63
import C13Global.Census.Source64
import C13Global.Census.Source65
import C13Global.Census.Source66
import C13Global.Census.Source67
import C13Global.Census.Source68
namespace C13.Global
open Finset C13.SourceData
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem all_catalog_foursets (K : Family Point) (hK : K ∈ catalog)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction K Q := by
  simp only [catalog,ordinary,List.mem_toFinset,ordinaryList,mem_insert,
    List.mem_cons,List.not_mem_nil,or_false] at hK
  rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Source68.all_foursets Q hQ
  · exact Source01.all_foursets Q hQ
  · exact Source02.all_foursets Q hQ
  · exact Source03.all_foursets Q hQ
  · exact Source04.all_foursets Q hQ
  · exact Source05.all_foursets Q hQ
  · exact Source06.all_foursets Q hQ
  · exact Source07.all_foursets Q hQ
  · exact Source08.all_foursets Q hQ
  · exact Source09.all_foursets Q hQ
  · exact Source10.all_foursets Q hQ
  · exact Source11.all_foursets Q hQ
  · exact Source12.all_foursets Q hQ
  · exact Source13.all_foursets Q hQ
  · exact Source14.all_foursets Q hQ
  · exact Source15.all_foursets Q hQ
  · exact Source16.all_foursets Q hQ
  · exact Source17.all_foursets Q hQ
  · exact Source18.all_foursets Q hQ
  · exact Source19.all_foursets Q hQ
  · exact Source20.all_foursets Q hQ
  · exact Source21.all_foursets Q hQ
  · exact Source22.all_foursets Q hQ
  · exact Source23.all_foursets Q hQ
  · exact Source24.all_foursets Q hQ
  · exact Source25.all_foursets Q hQ
  · exact Source26.all_foursets Q hQ
  · exact Source27.all_foursets Q hQ
  · exact Source28.all_foursets Q hQ
  · exact Source29.all_foursets Q hQ
  · exact Source30.all_foursets Q hQ
  · exact Source31.all_foursets Q hQ
  · exact Source32.all_foursets Q hQ
  · exact Source33.all_foursets Q hQ
  · exact Source34.all_foursets Q hQ
  · exact Source35.all_foursets Q hQ
  · exact Source36.all_foursets Q hQ
  · exact Source37.all_foursets Q hQ
  · exact Source38.all_foursets Q hQ
  · exact Source39.all_foursets Q hQ
  · exact Source40.all_foursets Q hQ
  · exact Source41.all_foursets Q hQ
  · exact Source42.all_foursets Q hQ
  · exact Source43.all_foursets Q hQ
  · exact Source44.all_foursets Q hQ
  · exact Source45.all_foursets Q hQ
  · exact Source46.all_foursets Q hQ
  · exact Source47.all_foursets Q hQ
  · exact Source48.all_foursets Q hQ
  · exact Source49.all_foursets Q hQ
  · exact Source50.all_foursets Q hQ
  · exact Source51.all_foursets Q hQ
  · exact Source52.all_foursets Q hQ
  · exact Source53.all_foursets Q hQ
  · exact Source54.all_foursets Q hQ
  · exact Source55.all_foursets Q hQ
  · exact Source56.all_foursets Q hQ
  · exact Source57.all_foursets Q hQ
  · exact Source58.all_foursets Q hQ
  · exact Source59.all_foursets Q hQ
  · exact Source60.all_foursets Q hQ
  · exact Source61.all_foursets Q hQ
  · exact Source62.all_foursets Q hQ
  · exact Source63.all_foursets Q hQ
  · exact Source64.all_foursets Q hQ
  · exact Source65.all_foursets Q hQ
  · exact Source66.all_foursets Q hQ
  · exact Source67.all_foursets Q hQ

/-- All finite internal obligations are discharged. Only the two separately
named published 1995 mathematical results remain theorem parameters. -/
theorem no_cover29 (hminimum : PublishedMinimumBound Point)
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
  apply all_catalog_foursets K hK Q (mem_powersetCard.mpr ⟨hQuniv,hQ⟩)
    hclass G hG hroot
  · intro q hq
    exact (mem_filter.mp (mem_erase.mp (hQM hq)).2).2
  · have hc := degree_add_outside G hole
    omega

theorem exact30_after_published_results (hminimum : PublishedMinimumBound Point)
    (hpublished : PublishedClassification1995) :
    (∃ F : Family Point, IsCoverOn univ F 7 4 ∧ F.card = 30) ∧
    (∀ F : Family Point, IsCoverOn univ F 7 4 → 30 ≤ F.card) := by
  refine ⟨exists_cover30,?_⟩
  intro F hF
  by_contra h
  have hs : F.card ≤ 29 := by omega
  obtain ⟨G,hG,_,h29⟩ := pad_cover_to29 F hF hs
  exact no_cover29 hminimum hpublished G hG h29

/-- The remaining published classification premise also supplies the minimum
bound through the independent, finite private-triple certificate. -/
theorem exact30_after_published_classification
    (hpublished : PublishedClassification1995) :
    (∃ F : Family Point, IsCoverOn univ F 7 4 ∧ F.card = 30) ∧
    (∀ F : Family Point, IsCoverOn univ F 7 4 → 30 ≤ F.card) :=
  exact30_after_published_results
    (minimum_bound_from_published_classification hpublished) hpublished

end C13.Global
