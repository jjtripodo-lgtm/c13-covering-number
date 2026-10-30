import C13Enumeration.Census.Figure6Alphabets
import C13Enumeration.Census.ColumnCertificate
import C13Enumeration.Census.CoverTree

namespace C13.Enumeration.Census
open Finset C13.Checker.RawSupport C13.SourceData
set_option Elab.async false
set_option maxRecDepth 10000

/-- Actual covering contradiction from an exact column certificate and a fully
checked integer branching tree. No enumerator flag or global census premise. -/
theorem figure6_cover_obstruction (Q : Finset Point) (hQ : Q ⊆ univ.erase hole)
    (columns : List Code) (witnesses : List (Option Point)) (tree : CoverTree)
    (column_check : columnsCertificateB columns Figure6Alphabets.alphabet Q witnesses = true)
    (tree_check : tree.check columns figure6 Q [] = true)
    (hclass : ClassifiesMinimumLinks catalog hole)
    (F : Family Point) (hcover : IsCoverOn univ F 7 4)
    (hroot : link F hole = figure6) (hmin : ∀ q ∈ Q, degree F q = 15)
    (houtside : (outside F hole).card ≤ 14) : False := by
  apply tree.sound columns figure6 Q [] tree_check F hcover hroot hQ hmin
  · intro b hb
    obtain ⟨B,hBF,rfl⟩ := mem_image.mp hb
    obtain ⟨hB,holeB⟩ := mem_outside.mp hBF
    apply columns_certificate_sound columns Figure6Alphabets.alphabet Q witnesses
      column_check (encodeTyped B)
    · exact encode_mem_blockCodes B (by
        intro p hp
        exact mem_erase.mpr ⟨by intro he; subst p; exact holeB hp,mem_univ _⟩)
        (hcover.1 B hB).2
    · intro q hq hqb
      have hqhole : q ≠ hole := (mem_erase.mp (hQ hq)).1
      have hp : pencil F hole q ∈ completeDomain catalog hole figure6 hole q := by
        rw [← hroot]
        exact actual_pencil_mem_completeDomain catalog hole hclass F hcover hqhole (hmin q hq)
      apply Figure6Alphabets.alphabet_complete q hqhole (pencil F hole q) hp B
      apply mem_pencil.mpr
      refine ⟨hB,holeB,?_⟩
      have hh := (mem_decodeTyped (encodeTyped B) q).2 hqb
      simpa using hh
  · intro x hx
    simp at hx
  · exact houtside

end C13.Enumeration.Census
