import C13Enumeration.TemplateSearch
namespace C13.Enumeration

def HasPairCount (S : Family Point) (n : Nat) : Prop :=
  ∃ a b : Point, a ≠ b ∧ coDegree S a b = n

instance (S : Family Point) (n : Nat) : Decidable (HasPairCount S n) :=
  inferInstanceAs (Decidable (∃ a b : Point, a ≠ b ∧ coDegree S a b = n))

theorem hasPairCount_transport (S T : Family Point) (e : Equiv.Perm Point)
    (he : transport e S = T) (n : Nat) : HasPairCount S n ↔ HasPairCount T n := by
  constructor
  · rintro ⟨a,b,hab,h⟩
    exact ⟨e a,e b,fun heq => hab (e.injective heq),(coDegree_transport S T e he a b).symm.trans h⟩
  · rintro ⟨a,b,hab,h⟩
    refine ⟨e.symm a,e.symm b,fun heq => hab (e.symm.injective heq),?_⟩
    rw [coDegree_transport S T e he,e.apply_symm_apply,e.apply_symm_apply]
    exact h
end C13.Enumeration
