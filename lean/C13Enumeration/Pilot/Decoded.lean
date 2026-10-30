import C13Enumeration.Pilot.Complete
import C13Covering.CheckerBridge
import C13Raw.Coding
namespace C13.Enumeration.Pilot
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Literal physical block codes, with the original point label carried in the domain. -/
def codedDomain : CodedDomain where
  point := 0
  alphabet := [1687, 2407, 2651, 1451, 3133, 973]
  rows := [[0,1,2,3,4,5]]

def codedRow : List (Fin codedDomain.alphabet.length) :=
  [⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩,⟨2,by decide +kernel⟩,
   ⟨3,by decide +kernel⟩,⟨4,by decide +kernel⟩,⟨5,by decide +kernel⟩]

theorem coded_point_checked : codedDomain.point = 0 := by rfl

theorem coded_rows_checked : codedDomain.rows.length = 1 := by rfl

theorem decoded_pencil_checked :
    RepresentsPencil (decodePencil (codedDomain.pencil codedRow)) expected := by
  unfold RepresentsPencil
  decide +kernel

/-- A complete point-labelled decoded raw domain in the checker's exact semantics. -/
theorem complete_decoded_domain :
    codedDomain.supported.domain.1 = (0 : Point).val ∧
    ∀ P ∈ completeDomain catalog hole link01 hole 0,
      ∃ p ∈ codedDomain.supported.domain.2, RepresentsPencil p P := by
  refine ⟨rfl,?_⟩
  intro P hP
  rw [complete_domain_eq_singleton] at hP
  have h := Finset.mem_singleton.mp hP
  subst P
  refine ⟨decodePencil (codedDomain.pencil codedRow),?_,decoded_pencil_checked⟩
  simp [CodedDomain.supported,CodedDomain.codes,decodeDomain,codedDomain,codedRow]

/-- The displayed row is also semantically possible; completeness is not vacuous. -/
theorem decoded_row_is_possible :
    ∃ P ∈ completeDomain catalog hole link01 hole 0,
      RepresentsPencil (decodePencil (codedDomain.pencil codedRow)) P :=
  ⟨expected,expected_mem_completeDomain,decoded_pencil_checked⟩
end C13.Enumeration.Pilot
