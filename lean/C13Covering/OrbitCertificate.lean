import C13Covering.OrbitRepresentatives

namespace C13.OrbitPilot.Certificate
open C13.OrbitPilot.Word

abbrev Entry := Fin 67 × List Generator

def EntryChecks (i : CompletionIndex) (entry : Entry) : Prop :=
  runWord entry.2 (representativeIndex entry.1) = i

instance (i : CompletionIndex) (entry : Entry) : Decidable (EntryChecks i entry) :=
  inferInstanceAs (Decidable (_ = _))

/-- Only bounded integer-index transitions are checked per certificate row.
The actual block-family image theorem follows from the checked generators and
the exact catalog representative identities, without native/compiler trust. -/
theorem entry_sound (i : CompletionIndex) (entry : Entry)
    (h : EntryChecks i entry) : CoveredIndex i :=
  covered_of_word i entry.1 entry.2 (Representatives.all_representatives entry.1) h

end C13.OrbitPilot.Certificate
