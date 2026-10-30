import C13Enumeration.PartialStar
namespace C13.Enumeration
set_option Elab.async false

def crossMapFinish (K T : Family Point) (hole c q : Point) (f : Point → Point) :
    List (Point → Point) :=
  if GoodMap K T hole c hole q f then [f] else []

theorem crossMapFinish_complete (K T : Family Point) (hole c q : Point)
    (e : Equiv.Perm Point) (he : e hole = q) (hc : e c = hole)
    (hs : transport e (link K c) = link T q) :
    (e : Point → Point) ∈ crossMapFinish K T hole c q e := by
  unfold crossMapFinish
  have h : GoodMap K T hole c hole q e :=
    ⟨e.bijective,he,hc,(mapFamily_equiv e _).trans hs⟩
  simp [h]

theorem cross_star_maps_complete (K T : Family Point) (hole c q : Point)
    (order : List Point) (hn : order.Nodup)
    (horder : ∀ x, x ∈ order ↔ x ≠ hole ∧ x ≠ c)
    (A B : Point → Point → Nat)
    (hA : ∀ a b, A a b = coDegree (link K c) a b)
    (hB : ∀ a b, B a b = coDegree (link T q) a b)
    (maps : List (Point → Point))
    (hbound : ∀ f ∈ assignSearch (starStep (link K c) (link T q) A B)
      (crossMapFinish K T hole c q) order (remainingPoints q hole) (anchorTable hole hole q), f ∈ maps)
    (e : Equiv.Perm Point) (he : e hole = q) (hc : e c = hole)
    (hs : transport e (link K c) = link T q) : (e : Point → Point) ∈ maps := by
  apply hbound
  apply assignSearch_complete _ _ e e.injective
    (starStep_safe _ _ A B hA hB e hs) _ _ _ hn
  · intro x hx
    obtain ⟨hxh,hxc⟩ := (horder x).mp hx
    apply (mem_remainingPoints q hole (e x)).mpr
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
  · exact crossMapFinish_complete K T hole c q e he hc hs
end C13.Enumeration
