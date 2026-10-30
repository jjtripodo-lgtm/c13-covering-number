import C13.CoverData
namespace C13.Checker
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def queries13_4 := queriesOf (List.range 13) 4

theorem known30_card : known30.toFinset.card = 30 := by decide +kernel

theorem known30_shape : ∀ b ∈ known30, b.card = 7 ∧ b ⊆ Finset.range 13 := by decide +kernel

def known30Witness : List Nat := [6, 6, 6, 6, 6, 17, 9, 8, 10, 4, 5, 19, 29, 13, 12, 17, 21, 23, 22, 16, 15, 19, 29, 24, 25, 17, 17, 17, 29, 28, 27, 20, 19, 19, 29, 0, 9, 23, 10, 16, 5, 2, 7, 13, 25, 9, 5, 10, 9, 9, 10, 5, 13, 5, 13, 16, 23, 18, 23, 28, 23, 16, 16, 25, 25, 20, 18, 18, 27, 20, 0, 6, 6, 6, 4, 6, 6, 6, 6, 6, 4, 8, 19, 8, 13, 8, 4, 4, 19, 13, 21, 15, 19, 21, 21, 25, 15, 19, 15, 25, 20, 19, 19, 26, 19, 0, 0, 0, 7, 13, 25, 7, 13, 25, 7, 20, 13, 3, 13, 13, 20, 14, 25, 25, 20, 20, 0, 21, 23, 10, 4, 5, 2, 29, 24, 25, 4, 5, 10, 29, 10, 10, 4, 4, 5, 29, 21, 23, 18, 21, 21, 22, 29, 24, 25, 24, 29, 18, 18, 26, 29, 0, 0, 0, 23, 10, 10, 5, 2, 2, 25, 5, 10, 3, 10, 5, 23, 18, 18, 23, 25, 18, 0, 0, 0, 21, 21, 25, 1, 4, 25, 25, 4, 4, 3, 26, 4, 21, 21, 25, 21, 25, 26, 0, 0, 0, 25, 25, 3, 25, 0, 9, 8, 10, 16, 15, 2, 29, 13, 12, 9, 8, 10, 8, 9, 8, 29, 13, 12, 12, 16, 15, 22, 29, 22, 22, 15, 16, 15, 29, 29, 28, 27, 26, 29, 0, 0, 0, 9, 9, 10, 16, 2, 2, 13, 9, 9, 10, 9, 13, 16, 14, 27, 27, 16, 27, 0, 0, 0, 8, 13, 8, 1, 13, 15, 13, 8, 13, 8, 8, 13, 15, 14, 15, 26, 15, 26, 0, 0, 0, 13, 13, 13, 14, 0, 0, 0, 29, 10, 10, 1, 2, 2, 29, 29, 10, 10, 10, 29, 29, 22, 22, 22, 29, 26, 0, 0, 0, 10, 2, 10, 28, 0, 0, 0, 26, 1, 26, 26, 0, 17, 21, 8, 22, 16, 5, 19, 7, 24, 12, 17, 5, 17, 8, 11, 8, 5, 19, 5, 12, 16, 17, 17, 21, 21, 22, 16, 16, 19, 24, 17, 17, 17, 27, 19, 16, 5, 18, 7, 11, 27, 5, 16, 5, 7, 5, 11, 3, 11, 5, 16, 14, 18, 27, 16, 18, 21, 8, 19, 7, 21, 8, 1, 19, 19, 7, 8, 19, 3, 8, 19, 21, 14, 19, 21, 19, 19, 7, 14, 3, 7, 7, 3, 14, 21, 5, 18, 21, 11, 22, 1, 24, 5, 24, 5, 11, 3, 11, 5, 21, 18, 18, 21, 24, 18, 5, 11, 3, 11, 5, 3, 18, 1, 21, 3, 21, 1, 3, 21, 3, 16, 8, 22, 8, 11, 8, 1, 16, 12, 12, 8, 11, 8, 8, 12, 16, 14, 22, 22, 16, 27, 16, 11, 27, 11, 16, 11, 14, 1, 14, 8, 8, 1, 8, 14, 14, 1, 11, 22, 11, 1, 11, 22, 11, 1, 6, 6, 6, 6, 4, 6, 2, 6, 6, 6, 4, 17, 17, 9, 9, 12, 4, 4, 12, 12, 17, 15, 17, 23, 24, 23, 15, 24, 15, 24, 17, 17, 17, 26, 20, 9, 23, 2, 7, 9, 23, 7, 2, 2, 7, 9, 9, 3, 9, 20, 20, 14, 23, 23, 20, 20, 4, 6, 6, 6, 6, 6, 1, 4, 6, 6, 4, 4, 3, 26, 4, 15, 14, 15, 26, 15, 20, 7, 14, 3, 7, 7, 3, 14, 4, 23, 2, 23, 24, 23, 1, 2, 2, 24, 4, 4, 3, 26, 4, 23, 24, 23, 23, 24, 26, 23, 2, 2, 23, 2, 3, 23, 1, 4, 3, 26, 1, 3, 26, 3, 9, 15, 2, 9, 9, 12, 1, 2, 2, 12, 9, 9, 12, 9, 12, 15, 14, 15, 26, 15, 26, 9, 2, 2, 9, 2, 9, 14, 1, 14, 15, 26, 1, 26, 14, 14, 1, 2, 2, 26, 1, 26, 26, 2, 1, 17, 17, 17, 7, 24, 12, 1, 24, 12, 7, 17, 17, 3, 12, 12, 17, 14, 17, 24, 24, 17, 7, 14, 3, 7, 7, 3, 14, 1, 14, 3, 7, 1, 3, 14, 3, 1, 24, 3, 24, 1, 3, 24, 3, 1, 1, 14, 12, 12, 1, 12, 14, 14, 1, 1]

theorem known30_witness_check : coverageWitnessB known30 queries13_4 known30Witness = true := by
  decide +kernel

theorem known30_coverage_check : coversB known30 queries13_4 = true :=
  (coversB_iff _ _).mpr (coverageWitness_sound _ _ _ known30_witness_check)

theorem known30_covers : ∀ q : Block, q ⊆ Finset.range 13 → q.card = 4 →
    ∃ b ∈ known30, q ⊆ b := by
  apply covers_all_of_complete known30 queries13_4 (Finset.range 13) 4
  · intro q hq hc
    apply queriesOf_complete (List.range 13) 4 q _ hc
    intro x hx
    exact List.mem_toFinset.mpr (List.mem_range.mpr (Finset.mem_range.mp (hq hx)))
  · exact known30_coverage_check

/-- The existing 30-block construction as an actual finite covering family. -/
theorem known30_upperBound : ∃ cover : Finset Block,
    cover.card = 30 ∧
    (∀ b ∈ cover, b.card = 7 ∧ b ⊆ Finset.range 13) ∧
    (∀ q : Block, q ⊆ Finset.range 13 → q.card = 4 → ∃ b ∈ cover, q ⊆ b) := by
  refine ⟨known30.toFinset, known30_card, ?_, ?_⟩
  · intro b hb
    exact known30_shape b (List.mem_toFinset.mp hb)
  · intro q hq hc
    obtain ⟨b,hb,hsub⟩ := known30_covers q hq hc
    exact ⟨b,List.mem_toFinset.mpr hb,hsub⟩

#print axioms known30_card
#print axioms known30_shape
#print axioms known30_witness_check
#print axioms known30_coverage_check
#print axioms known30_covers
#print axioms known30_upperBound
end C13.Checker
