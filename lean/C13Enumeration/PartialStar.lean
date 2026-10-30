import C13Enumeration.PairInvariant
namespace C13.Enumeration
open Finset

/-- Every source block must still have a target block with the same incidence
pattern on the assigned points. Empty incidence columns remain in the universe. -/
def partialMatch (S T : Family Point) (remaining : List Point) (f : Point → Point) : Bool :=
  letI (B : Finset Point) : Decidable (∃ C ∈ T, ∀ x : Point,
      x ∉ remaining → (x ∈ B ↔ f x ∈ C)) := Finset.decidableExistsAndFinset
  @decide (∀ B ∈ S, ∃ C ∈ T, ∀ x : Point, x ∉ remaining → (x ∈ B ↔ f x ∈ C))
    Finset.decidableDforallFinset

theorem partialMatch_safe (S T : Family Point) (e : Equiv.Perm Point)
    (he : transport e S = T) (remaining : List Point) (f : Point → Point)
    (hf : AgreesOff remaining f e) : partialMatch S T remaining f = true := by
  simp only [partialMatch,decide_eq_true_eq]
  intro B hB
  refine ⟨B.map e.toEmbedding,?_,?_⟩
  · rw [← he]
    exact mem_image.mpr ⟨B,hB,rfl⟩
  · intro x hx
    rw [hf x hx]
    simp

theorem agreesOff_put (e f : Point → Point) (x : Point) (xs : List Point)
    (h : AgreesOff (x :: xs) f e) : AgreesOff xs (put f x (e x)) e := by
  intro a ha
  by_cases hax : a = x
  · subst a
    simp
  · rw [put_ne _ _ _ hax]
    exact h a (by simp [ha,hax])

def starStep (S T : Family Point) (A B : Point → Point → Nat)
    (remaining : List Point) (f : Point → Point) (a b : Point) : Bool :=
  matrixStep (List.finRange 13) A B remaining f a b &&
    partialMatch S T remaining.tail (put f a b)

theorem starStep_safe (S T : Family Point) (A B : Point → Point → Nat)
    (hA : ∀ a b, A a b = coDegree S a b) (hB : ∀ a b, B a b = coDegree T a b)
    (e : Equiv.Perm Point) (he : transport e S = T)
    (x : Point) (xs : List Point) (f : Point → Point)
    (hf : AgreesOff (x :: xs) f e) : starStep S T A B (x :: xs) f x (e x) = true := by
  simp only [starStep,Bool.and_eq_true]
  constructor
  · exact matrixStep_safe _ A B e
      (fun a b => by rw [hA,hB]; exact coDegree_transport S T e he a b) x xs f hf
  · exact partialMatch_safe S T e he xs (put f x (e x)) (agreesOff_put e f x xs hf)

/-- Strong pruned template enumeration has the same unrestricted completeness
contract as the base backtracker. -/
theorem star_template_maps_complete (K : Family Point) (hole c : Point)
    (order : List Point) (hn : order.Nodup)
    (horder : ∀ x, x ∈ order ↔ x ≠ hole ∧ x ≠ c)
    (A : Point → Point → Nat) (hA : ∀ a b, A a b = coDegree (link K c) a b)
    (maps : List (Point → Point))
    (hbound : ∀ f ∈ assignSearch (starStep (link K c) (link K c) A A)
      (mapFinish K hole c) order (remainingPoints c hole) (anchorTable hole hole c), f ∈ maps)
    (e : Equiv.Perm Point) (he : e hole = c) (hc : e c = hole)
    (hs : transport e (link K c) = link K c) : (e : Point → Point) ∈ maps := by
  apply hbound
  apply assignSearch_complete _ _ e e.injective
    (starStep_safe _ _ A A hA hA e hs) _ _ _ hn
  · intro x hx
    obtain ⟨hxh,hxc⟩ := (horder x).mp hx
    apply (mem_remainingPoints c hole (e x)).mpr
    constructor
    · intro h
      exact hxh (e.injective (h.trans he.symm))
    · intro h
      exact hxc (e.injective (h.trans hc.symm))
  · intro x hx
    by_cases hxh : x = hole
    · subst x
      simp [anchorTable,he]
    · have hxc : x = c := by
        by_contra h
        exact hx ((horder x).mpr ⟨hxh,h⟩)
      subst x
      simp [anchorTable,hxh,hc]
  · exact mapFinish_complete K hole c e he hc hs
end C13.Enumeration
