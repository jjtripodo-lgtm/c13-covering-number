import C13Covering.SourceLiterals
import C13Covering.PositiveBridge

/-! Literal Figure-1 completion universe plus separate exceptional Figure 6.
These are data definitions. The 1995 classification remains an explicit Prop
parameter; defining its statement does not prove or postulate it. -/
namespace C13.SourceData
open Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def figure1Core : Family Point := {{0, 1, 4, 5, 8, 9}, {0, 1, 6, 7, 10, 11}, {2, 3, 4, 5, 10, 11}, {2, 3, 6, 7, 8, 9}, {0, 2, 4, 6, 8, 10}, {0, 2, 5, 7, 9, 11}, {1, 3, 4, 6, 9, 11}, {1, 3, 5, 7, 8, 10}, {0, 3, 4, 7, 8, 11}, {0, 3, 5, 6, 9, 10}, {1, 2, 4, 7, 9, 10}, {1, 2, 5, 6, 8, 11}}

def short0 : Finset Point := {0,1,2,3}
def short1 : Finset Point := {4,5,6,7}
def short2 : Finset Point := {8,9,10,11}

def completionChoices (short : Finset Point) : Finset (Finset Point) :=
  ((univ.erase hole) \ short).powersetCard 2

def figure1Completion (A B C : Finset Point) : Family Point :=
  figure1Core ∪ {short0 ∪ A, short1 ∪ B, short2 ∪ C}

def rawOrdinary : Finset (Family Point) :=
  (completionChoices short0).biUnion fun A =>
    (completionChoices short1).biUnion fun B =>
      (completionChoices short2).image fun C => figure1Completion A B C

def rawSources : Finset (Family Point) := insert figure6 rawOrdinary

theorem mem_rawOrdinary (L : Family Point) : L ∈ rawOrdinary ↔
    ∃ A ∈ completionChoices short0, ∃ B ∈ completionChoices short1,
      ∃ C ∈ completionChoices short2, figure1Completion A B C = L := by
  simp [rawOrdinary]

theorem figure6_mem_rawSources : figure6 ∈ rawSources := mem_insert_self ..

theorem completionChoices_counts :
    (completionChoices short0).card = 28 ∧
    (completionChoices short1).card = 28 ∧
    (completionChoices short2).card = 28 := by
  decide +kernel

/-- Number of literal completion triples. This does not assert an isomorphism
classification or completeness of the compressed catalog. -/
theorem literal_completion_triple_count :
    (completionChoices short0).card * (completionChoices short1).card *
      (completionChoices short2).card = 21952 := by
  rw [completionChoices_counts.1,completionChoices_counts.2.1,completionChoices_counts.2.2]

/-- The precise formal statement used for the external 1995 Theorem 5.9.
It refers to the literal complete Figure-1 family AND exceptional Figure 6. -/
def PublishedClassification1995 : Prop := ClassifiesMinimumLinks rawSources hole

/-- Current milestone interface, explicitly conditional on three unfinished
internal finite proofs. Do not report this as a completed exact theorem. -/
theorem exact30_of_remaining_finite_obligations
    (D : Family Point → Point → List Checker.Pencil)
    (hminimum : PublishedMinimumBound Point)
    (hpublished : PublishedClassification1995)
    (hcoverage : CatalogCoversSources rawSources catalog hole)
    (hcomplete : ExecutableDomainsComplete catalog hole D)
    (hchecks : AllFourChecksFalse catalog hole D) :
    (∃ F : Family Point, IsCoverOn univ F 7 4 ∧ F.card = 30) ∧
    (∀ F : Family Point, IsCoverOn univ F 7 4 → 30 ≤ F.card) :=
  exact30_from_complete_checked_domains rawSources catalog hole D
    hminimum hpublished hcoverage hcomplete hchecks

end C13.SourceData
