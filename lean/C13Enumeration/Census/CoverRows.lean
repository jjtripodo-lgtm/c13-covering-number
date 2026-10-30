import C13Enumeration.Census.DualCertificate
import C13Enumeration.Canonical.Complete

namespace C13.Enumeration.Census
open Finset C13.Checker.RawSupport C13.SourceData
set_option Elab.async false
set_option maxRecDepth 10000

theorem link_star_comm (F : Family Point) (r q : Point) (hqr : q ≠ r) :
    link (star F q) r = star (link F r) q := by
  ext B
  constructor
  · intro hB
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hB
    obtain ⟨hAFq,hrA⟩ := mem_star.mp hA
    obtain ⟨hAF,hqA⟩ := mem_star.mp hAFq
    exact mem_star.mpr ⟨mem_image.mpr ⟨A,mem_star.mpr ⟨hAF,hrA⟩,rfl⟩,
      mem_erase.mpr ⟨hqr,hqA⟩⟩
  · intro hB
    obtain ⟨hB,hqB⟩ := mem_star.mp hB
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hB
    obtain ⟨hAF,hrA⟩ := mem_star.mp hA
    exact mem_image.mpr ⟨A,mem_star.mpr ⟨mem_star.mpr ⟨hAF,(mem_erase.mp hqB).2⟩,hrA⟩,rfl⟩

theorem pencil_card_add_root_degree (F : Family Point) (r q : Point) (hqr : q ≠ r) :
    (pencil F r q).card + degree (link F r) q = degree F q := by
  have h := degree_add_outside (star F q) r
  rw [← link_card,link_star_comm F r q hqr] at h
  have he : outside (star F q) r = pencil F r q := by
    ext B
    simp [and_assoc,and_left_comm,and_comm]
  rw [he] at h
  change degree (link F r) q + (pencil F r q).card = degree F q at h
  omega

theorem required_quad_covered_outside (F K : Family Point)
    (hcover : IsCoverOn univ F 7 4) (hroot : link F hole = K)
    (T : Finset Point) (hT : T ⊆ univ.erase hole) (hcard : T.card = 4)
    (uncovered : ∀ A ∈ K, ¬ T ⊆ A) :
    ∃ B ∈ outside F hole, T ⊆ B := by
  obtain ⟨B,hBF,hTB⟩ := hcover.2 T (subset_univ _) hcard
  have hn : hole ∉ B := by
    intro hh
    have he : B.erase hole ∈ K := by
      rw [← hroot]
      exact mem_image.mpr ⟨B,mem_star.mpr ⟨hBF,hh⟩,rfl⟩
    apply uncovered _ he
    intro p hp
    exact mem_erase.mpr ⟨(mem_erase.mp (hT hp)).1,hTB hp⟩
  exact ⟨B,mem_outside.mpr ⟨hBF,hn⟩,hTB⟩

def outsideCodes (F : Family Point) : Finset Code := (outside F hole).image encodeTyped

@[simp] theorem outsideCodes_card (F : Family Point) :
    (outsideCodes F).card = (outside F hole).card :=
  card_image_of_injective _ encodeTyped_injective

theorem actual_block_in_lookup_alphabet (F K : Family Point)
    (hK : K ∈ catalog) (q : Point) (hq : q ≠ hole)
    (hp : pencil F hole q ∈ completeDomain catalog hole K hole q)
    (b : Code) (hb : b ∈ outsideCodes F) (hqb : b.getLsbD q.val = true) :
    b ∈ (Canonical.codedDomains K q).alphabet := by
  obtain ⟨B,hBF,rfl⟩ := mem_image.mp hb
  have hqB : q ∈ B := by
    have hh := (mem_decodeTyped (encodeTyped B) q).2 hqb
    simpa using hh
  apply represented_block_in_alphabet (Canonical.codedDomains K q)
    (pencil F hole q) (Canonical.all_domains_complete K hK q hq _ hp) B
  obtain ⟨hB,holeB⟩ := mem_outside.mp hBF
  exact mem_pencil.mpr ⟨hB,holeB,hqB⟩

end C13.Enumeration.Census
