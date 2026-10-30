import C13Enumeration.FastSearch
namespace C13.Enumeration
open Finset

/-- Includes degree zero, so isolated ambient labels contribute to the signature. -/
def degreeCount (S : Family Point) (k : Nat) : Nat :=
  (Finset.univ.filter fun a : Point => coDegree S a a = k).card

theorem degreeCount_transport (S T : Family Point) (e : Equiv.Perm Point)
    (he : transport e S = T) (k : Nat) : degreeCount S k = degreeCount T k := by
  unfold degreeCount
  apply Finset.card_bij (fun a _ => e a)
  · intro a ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [← coDegree_transport S T e he]
    exact (Finset.mem_filter.mp ha).2
  · intro a ha b hb hab
    exact e.injective hab
  · intro b hb
    refine ⟨e.symm b,?_,e.apply_symm_apply b⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [coDegree_transport S T e he,e.apply_symm_apply]
    exact (Finset.mem_filter.mp hb).2

def degreeSignature (S : Family Point) : List Nat :=
  (List.range 14).map (degreeCount S)

theorem degreeSignature_transport (S T : Family Point) (e : Equiv.Perm Point)
    (he : transport e S = T) : degreeSignature S = degreeSignature T := by
  unfold degreeSignature
  apply List.map_congr_left
  intro k hk
  exact degreeCount_transport S T e he k

theorem not_star_iso_of_signature (S T : Family Point)
    (h : degreeSignature S ≠ degreeSignature T) (e : Equiv.Perm Point) :
    transport e S ≠ T := fun he => h (degreeSignature_transport S T e he)

end C13.Enumeration
