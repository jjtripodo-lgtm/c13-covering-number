import C13Covering.SourceFigures
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod

/-! Complete raw Figure-1 indexing. All 28³ labeled completion triples are
indexed. The proof is surjective onto the literal family; no orbit quotient,
nonisomorphism claim, or executable-domain assumption is used. -/
namespace C13.OrbitPilot
open Finset
open SourceData
set_option maxRecDepth 10000
set_option maxHeartbeats 0

abbrev CompletionIndex := Fin 28 × Fin 28 × Fin 28

def choice0 : Fin 28 → Finset Point :=
  ![{4,5}, {4,6}, {4,7}, {4,8}, {4,9}, {4,10}, {4,11}, {5,6}, {5,7}, {5,8}, {5,9}, {5,10}, {5,11}, {6,7}, {6,8}, {6,9}, {6,10}, {6,11}, {7,8}, {7,9}, {7,10}, {7,11}, {8,9}, {8,10}, {8,11}, {9,10}, {9,11}, {10,11}]

theorem choice0_complete : univ.image choice0 = completionChoices short0 := by
  decide +kernel

def choice1 : Fin 28 → Finset Point :=
  ![{0,1}, {0,2}, {0,3}, {0,8}, {0,9}, {0,10}, {0,11}, {1,2}, {1,3}, {1,8}, {1,9}, {1,10}, {1,11}, {2,3}, {2,8}, {2,9}, {2,10}, {2,11}, {3,8}, {3,9}, {3,10}, {3,11}, {8,9}, {8,10}, {8,11}, {9,10}, {9,11}, {10,11}]

theorem choice1_complete : univ.image choice1 = completionChoices short1 := by
  decide +kernel

def choice2 : Fin 28 → Finset Point :=
  ![{0,1}, {0,2}, {0,3}, {0,4}, {0,5}, {0,6}, {0,7}, {1,2}, {1,3}, {1,4}, {1,5}, {1,6}, {1,7}, {2,3}, {2,4}, {2,5}, {2,6}, {2,7}, {3,4}, {3,5}, {3,6}, {3,7}, {4,5}, {4,6}, {4,7}, {5,6}, {5,7}, {6,7}]

theorem choice2_complete : univ.image choice2 = completionChoices short2 := by
  decide +kernel

def indexedCompletion (i : CompletionIndex) : Family Point :=
  figure1Completion (choice0 i.1) (choice1 i.2.1) (choice2 i.2.2)

def allIndices : Finset CompletionIndex := univ

theorem every_index_enumerated (i : CompletionIndex) : i ∈ allIndices := mem_univ i

theorem allIndices_card : allIndices.card = 21952 := by
  simp [allIndices,Fintype.card_prod,Fintype.card_fin]

theorem indexedCompletion_mem_raw (i : CompletionIndex) : indexedCompletion i ∈ rawOrdinary := by
  apply (mem_rawOrdinary _).mpr
  refine ⟨choice0 i.1,?_,choice1 i.2.1,?_,choice2 i.2.2,?_,rfl⟩
  · rw [← choice0_complete]
    exact mem_image.mpr ⟨i.1,mem_univ _,rfl⟩
  · rw [← choice1_complete]
    exact mem_image.mpr ⟨i.2.1,mem_univ _,rfl⟩
  · rw [← choice2_complete]
    exact mem_image.mpr ⟨i.2.2,mem_univ _,rfl⟩

theorem raw_completion_has_index (L : Family Point) (hL : L ∈ rawOrdinary) :
    ∃ i : CompletionIndex, indexedCompletion i = L := by
  obtain ⟨A,hA,B,hB,C,hC,hL⟩ := (mem_rawOrdinary L).mp hL
  rw [← choice0_complete] at hA
  rw [← choice1_complete] at hB
  rw [← choice2_complete] at hC
  obtain ⟨a,_,rfl⟩ := mem_image.mp hA
  obtain ⟨b,_,rfl⟩ := mem_image.mp hB
  obtain ⟨c,_,rfl⟩ := mem_image.mp hC
  exact ⟨(a,b,c),hL⟩

/-- Exhaustive labeled enumeration proved without evaluating the 21,952-family
union. Surjectivity, not full-S12 nonisomorphism, is exactly what coverage needs. -/
theorem rawOrdinary_eq_indexed_image : rawOrdinary = allIndices.image indexedCompletion := by
  ext L
  constructor
  · intro hL
    obtain ⟨i,hi⟩ := raw_completion_has_index L hL
    exact mem_image.mpr ⟨i,every_index_enumerated i,hi⟩
  · intro hL
    obtain ⟨i,_,rfl⟩ := mem_image.mp hL
    exact indexedCompletion_mem_raw i

/-- The source classification has two branches, with the exceptional figure
included independently of the complete ordinary index space. -/
theorem rawSources_eq_exception_and_indices :
    rawSources = insert figure6 (allIndices.image indexedCompletion) := by
  unfold rawSources
  rw [rawOrdinary_eq_indexed_image]

def catalogRepresentative (i : Fin 67) : Family Point :=
  ordinaryList[i.val]'(by rw [ordinaryList_length]; exact i.isLt)

theorem catalogRepresentative_mem (i : Fin 67) : catalogRepresentative i ∈ catalog := by
  apply ordinary_subset_catalog
  apply List.mem_toFinset.mpr
  exact List.getElem_mem (by rw [ordinaryList_length]; exact i.isLt)

/-- A single proof-carrying orbit witness. This proposition neither enumerates
permutations nor assumes the construction group is the full automorphism group. -/
def CoveredIndex (i : CompletionIndex) : Prop :=
  ∃ (j : Fin 67) (e : Equiv.Perm Point),
    e hole = hole ∧ transport e (catalogRepresentative j) = indexedCompletion i

/-- Once every explicit index has a checked witness, the complete ordinary
source coverage follows; no sample or count can replace this universal input. -/
theorem ordinary_coverage_of_all_index_witnesses
    (h : ∀ i : CompletionIndex, CoveredIndex i) :
    CatalogCoversSources rawOrdinary catalog hole := by
  intro S hS
  obtain ⟨i,rfl⟩ := raw_completion_has_index S hS
  obtain ⟨j,e,he,hE⟩ := h i
  exact ⟨catalogRepresentative j,catalogRepresentative_mem j,e,he,hE⟩

theorem full_coverage_of_all_index_witnesses
    (h : ∀ i : CompletionIndex, CoveredIndex i) :
    CatalogCoversSources rawSources catalog hole :=
  cover_sources_with_exception rawOrdinary catalog figure6 hole
    (ordinary_coverage_of_all_index_witnesses h) figure6_mem_catalog

end C13.OrbitPilot
