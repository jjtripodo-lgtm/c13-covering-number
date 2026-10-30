import C13Global.PrivateData.Part00
import C13Global.PrivateData.Part01
import C13Global.PrivateData.Part02
import C13Global.PrivateData.Part03
import C13Global.PrivateData.Part04
import C13Global.PrivateData.Part05
import C13Global.PrivateData.Part06
import C13Global.PrivateData.Part07
import C13Global.PrivateData.Part08
namespace C13.Global
open Finset C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- All 1,020 catalog blocks have explicit, kernel-checked private triples. -/
theorem catalog_private_triples : ∀ K ∈ catalog, PrivateTriples K := by
  intro K hK
  simp only [catalog,ordinary,List.mem_toFinset,ordinaryList,mem_insert,
    List.mem_cons,List.not_mem_nil,or_false] at hK
  rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PrivateData.private68
  · exact PrivateData.private01
  · exact PrivateData.private02
  · exact PrivateData.private03
  · exact PrivateData.private04
  · exact PrivateData.private05
  · exact PrivateData.private06
  · exact PrivateData.private07
  · exact PrivateData.private08
  · exact PrivateData.private09
  · exact PrivateData.private10
  · exact PrivateData.private11
  · exact PrivateData.private12
  · exact PrivateData.private13
  · exact PrivateData.private14
  · exact PrivateData.private15
  · exact PrivateData.private16
  · exact PrivateData.private17
  · exact PrivateData.private18
  · exact PrivateData.private19
  · exact PrivateData.private20
  · exact PrivateData.private21
  · exact PrivateData.private22
  · exact PrivateData.private23
  · exact PrivateData.private24
  · exact PrivateData.private25
  · exact PrivateData.private26
  · exact PrivateData.private27
  · exact PrivateData.private28
  · exact PrivateData.private29
  · exact PrivateData.private30
  · exact PrivateData.private31
  · exact PrivateData.private32
  · exact PrivateData.private33
  · exact PrivateData.private34
  · exact PrivateData.private35
  · exact PrivateData.private36
  · exact PrivateData.private37
  · exact PrivateData.private38
  · exact PrivateData.private39
  · exact PrivateData.private40
  · exact PrivateData.private41
  · exact PrivateData.private42
  · exact PrivateData.private43
  · exact PrivateData.private44
  · exact PrivateData.private45
  · exact PrivateData.private46
  · exact PrivateData.private47
  · exact PrivateData.private48
  · exact PrivateData.private49
  · exact PrivateData.private50
  · exact PrivateData.private51
  · exact PrivateData.private52
  · exact PrivateData.private53
  · exact PrivateData.private54
  · exact PrivateData.private55
  · exact PrivateData.private56
  · exact PrivateData.private57
  · exact PrivateData.private58
  · exact PrivateData.private59
  · exact PrivateData.private60
  · exact PrivateData.private61
  · exact PrivateData.private62
  · exact PrivateData.private63
  · exact PrivateData.private64
  · exact PrivateData.private65
  · exact PrivateData.private66
  · exact PrivateData.private67

theorem private_witness_count : PrivateData.witnesses01.length + PrivateData.witnesses02.length + PrivateData.witnesses03.length + PrivateData.witnesses04.length + PrivateData.witnesses05.length + PrivateData.witnesses06.length + PrivateData.witnesses07.length + PrivateData.witnesses08.length + PrivateData.witnesses09.length + PrivateData.witnesses10.length + PrivateData.witnesses11.length + PrivateData.witnesses12.length + PrivateData.witnesses13.length + PrivateData.witnesses14.length + PrivateData.witnesses15.length + PrivateData.witnesses16.length + PrivateData.witnesses17.length + PrivateData.witnesses18.length + PrivateData.witnesses19.length + PrivateData.witnesses20.length + PrivateData.witnesses21.length + PrivateData.witnesses22.length + PrivateData.witnesses23.length + PrivateData.witnesses24.length + PrivateData.witnesses25.length + PrivateData.witnesses26.length + PrivateData.witnesses27.length + PrivateData.witnesses28.length + PrivateData.witnesses29.length + PrivateData.witnesses30.length + PrivateData.witnesses31.length + PrivateData.witnesses32.length + PrivateData.witnesses33.length + PrivateData.witnesses34.length + PrivateData.witnesses35.length + PrivateData.witnesses36.length + PrivateData.witnesses37.length + PrivateData.witnesses38.length + PrivateData.witnesses39.length + PrivateData.witnesses40.length + PrivateData.witnesses41.length + PrivateData.witnesses42.length + PrivateData.witnesses43.length + PrivateData.witnesses44.length + PrivateData.witnesses45.length + PrivateData.witnesses46.length + PrivateData.witnesses47.length + PrivateData.witnesses48.length + PrivateData.witnesses49.length + PrivateData.witnesses50.length + PrivateData.witnesses51.length + PrivateData.witnesses52.length + PrivateData.witnesses53.length + PrivateData.witnesses54.length + PrivateData.witnesses55.length + PrivateData.witnesses56.length + PrivateData.witnesses57.length + PrivateData.witnesses58.length + PrivateData.witnesses59.length + PrivateData.witnesses60.length + PrivateData.witnesses61.length + PrivateData.witnesses62.length + PrivateData.witnesses63.length + PrivateData.witnesses64.length + PrivateData.witnesses65.length + PrivateData.witnesses66.length + PrivateData.witnesses67.length + PrivateData.witnesses68.length = 1020 := by decide +kernel

/-- This removes the separately supplied minimum-bound premise, conditional
on the existing published classification statement and checked source coverage.
It does not independently prove that published classification. -/
theorem minimum_bound_from_published_classification
    (hpublished : PublishedClassification1995) : PublishedMinimumBound Point :=
  minimum_bound_of_classified_private_triples
    (classification_of_source_coverage rawSources catalog hole hpublished
      C13.OrbitPilot.AllSources.catalog_covers_all_raw_sources)
    catalog_private_triples
#print axioms minimum_bound_from_published_classification
end C13.Global
