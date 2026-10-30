import C13Covering.CheckerBridge
import C13.Known30

namespace C13
open Finset

def decodeBlock (B : Finset ℕ) : Finset Point := univ.filter (fun q => q.val ∈ B)

@[simp] theorem mem_decodeBlock (q : Point) (B : Finset ℕ) :
    q ∈ decodeBlock B ↔ q.val ∈ B := by simp [decodeBlock]

@[simp] theorem encodeBlock_card (B : Finset Point) : (encodeBlock B).card = B.card := card_map _

theorem encodeBlock_subset_range (B : Finset Point) : encodeBlock B ⊆ range 13 := by
  intro n hn
  obtain ⟨q,_,rfl⟩ := mem_map.mp hn
  exact mem_range.mpr q.isLt

theorem encode_decodeBlock (B : Finset ℕ) (hB : B ⊆ range 13) :
    encodeBlock (decodeBlock B) = B := by
  ext n
  constructor
  · intro hn
    obtain ⟨q,hq,rfl⟩ := mem_map.mp hn
    exact (mem_decodeBlock q B).mp hq
  · intro hn
    have hlt : n < 13 := mem_range.mp (hB hn)
    exact mem_map.mpr ⟨⟨n,hlt⟩,(mem_decodeBlock ⟨n,hlt⟩ B).mpr hn,rfl⟩

theorem decodeBlock_card (B : Finset ℕ) (hB : B ⊆ range 13) :
    (decodeBlock B).card = B.card := by
  rw [← encodeBlock_card,encode_decodeBlock B hB]

/-- The exact positive control provided by the independent literal checker,
transported to the same Fin13/simple-family semantics as the lower reduction. -/
def known30Typed : Family Point := Checker.known30.toFinset.image decodeBlock

theorem known30Typed_card : known30Typed.card = 30 := by
  rw [known30Typed,← Checker.known30_card]
  apply card_image_iff.mpr
  intro A hA B hB heq
  have ha := (Checker.known30_shape A (List.mem_toFinset.mp hA)).2
  have hb := (Checker.known30_shape B (List.mem_toFinset.mp hB)).2
  have hh := congrArg encodeBlock heq
  simpa only [encode_decodeBlock A ha,encode_decodeBlock B hb] using hh

theorem known30Typed_isCover : IsCoverOn univ known30Typed 7 4 := by
  constructor
  · intro B hB
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hB
    have ha := Checker.known30_shape A (List.mem_toFinset.mp hA)
    exact ⟨subset_univ _,(decodeBlock_card A ha.2).trans ha.1⟩
  · intro T _ hT
    obtain ⟨B,hB,hTB⟩ := Checker.known30_covers (encodeBlock T)
      (encodeBlock_subset_range T) (by simpa using hT)
    refine ⟨decodeBlock B,mem_image.mpr ⟨B,List.mem_toFinset.mpr hB,rfl⟩,?_⟩
    intro q hq
    exact (mem_decodeBlock q B).mpr (hTB ((mem_encodeBlock q T).mpr hq))

theorem exists_cover30 : ∃ F : Family Point, IsCoverOn univ F 7 4 ∧ F.card = 30 :=
  ⟨known30Typed,known30Typed_isCover,known30Typed_card⟩

/-- A completed proof must still supply ALL three internal finite obligations.
The positive half is unconditional and comes from the literal 30-cover. -/
theorem exact30_from_complete_checked_domains
    (sources catalog : Finset (Family Point)) (hole : Point)
    (D : Family Point → Point → List Checker.Pencil)
    (hminimum : PublishedMinimumBound Point)
    (hpublished : ClassifiesMinimumLinks sources hole)
    (hcoverage : CatalogCoversSources sources catalog hole)
    (hcomplete : ExecutableDomainsComplete catalog hole D)
    (hchecks : AllFourChecksFalse catalog hole D) :
    (∃ F : Family Point, IsCoverOn univ F 7 4 ∧ F.card = 30) ∧
    (∀ F : Family Point, IsCoverOn univ F 7 4 → 30 ≤ F.card) :=
  ⟨exists_cover30, fun F hF => cover_card_ge30_from_complete_checked_domains
    sources catalog hole D hminimum hpublished hcoverage hcomplete hchecks F hF⟩

end C13
