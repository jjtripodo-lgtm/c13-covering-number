import C13Enumeration.TemplateTransport
namespace C13.Enumeration

/-- Point maps are retained extensionally on all thirteen ambient labels. -/
def mapFinish (K : Family Point) (hole c : Point) (f : Point → Point) :
    List (Point → Point) :=
  if GoodMap K K hole c hole c f then [f] else []

theorem mapFinish_complete (K : Family Point) (hole c : Point)
    (e : Equiv.Perm Point) (he : e hole = c) (hc : e c = hole)
    (hs : transport e (link K c) = link K c) :
    (e : Point → Point) ∈ mapFinish K hole c e := by
  unfold mapFinish
  have h : GoodMap K K hole c hole c e :=
    ⟨e.bijective,he,hc,(mapFamily_equiv e _).trans hs⟩
  simp [h]

theorem assignSearch_map_bound_cons {R : (Point → Point) → Prop}
    (step : List Point → (Point → Point) → Point → Point → Bool)
    (finish : (Point → Point) → List (Point → Point))
    (x : Point) (xs ys allowed : List Point) (f : Point → Point)
    (hallowed : ∀ y ∈ ys, step (x :: xs) f x y = true → y ∈ allowed)
    (hchildren : ∀ y ∈ allowed, ∀ z ∈ assignSearch step finish xs (ys.erase y) (put f x y), R z) :
    ∀ z ∈ assignSearch step finish (x :: xs) ys f, R z := by
  intro z hz
  obtain ⟨y,hy,hz⟩ := List.mem_flatMap.mp hz
  split at hz
  · rename_i hstep
    exact hchildren y (hallowed y hy hstep) z hz
  · simp at hz

theorem list_all_maps_bound (xs maps : List (Point → Point))
    (h : (xs.all fun f => decide (f ∈ maps)) = true) : ∀ f ∈ xs, f ∈ maps := by
  intro f hf
  exact of_decide_eq_true ((List.all_eq_true.mp h) f hf)

/-- Kernel-checked finite templates control every unrestricted anchored star
map, including permutations inside degree-zero incidence fibers. -/
theorem template_maps_complete (K : Family Point) (hole c : Point)
    (order : List Point) (hn : order.Nodup)
    (horder : ∀ x, x ∈ order ↔ x ≠ hole ∧ x ≠ c)
    (A : Point → Point → Nat) (hA : ∀ a b, A a b = coDegree (link K c) a b)
    (maps : List (Point → Point))
    (hbound : ∀ f ∈ assignSearch (matrixStep (List.finRange 13) A A)
      (mapFinish K hole c) order (remainingPoints c hole) (anchorTable hole hole c), f ∈ maps)
    (e : Equiv.Perm Point) (he : e hole = c) (hc : e c = hole)
    (hs : transport e (link K c) = link K c) : (e : Point → Point) ∈ maps := by
  apply hbound
  apply assignSearch_complete _ _ e e.injective
    (matrixStep_safe _ A A e (fun a b => by rw [hA,hA]; exact coDegree_transport _ _ e hs a b))
    _ _ _ hn
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

/-- A normalizer fixing the omitted source point transports a full arbitrary
source map to the anchored template maps without selecting a subgroup. -/
theorem source_map_factors (K T : Family Point) (hole c q : Point)
    (a e : Equiv.Perm Point) (ha : a hole = hole) (hac : a c = q)
    (hs : transport a (link K c) = link T q)
    (he : e hole = q) (hec : e c = hole)
    (hes : transport e (link K c) = link T q) :
    let g := a.symm.trans e
    g hole = q ∧ g q = hole ∧ transport g (link T q) = link T q ∧
      ∀ x, g (a x) = e x := by
  dsimp
  have hah : a.symm hole = hole := by
    apply a.injective
    simp [ha]
  have haq : a.symm q = c := by
    apply a.injective
    simp [hac]
  refine ⟨by simpa [hah] using he,by simpa [haq] using hec,?_,?_⟩
  · rw [transport_trans]
    have hback : transport a.symm (link T q) = link K c := by rw [← hs,transport_inverse]
    rw [hback]
    exact hes
  · intro x
    simp

end C13.Enumeration
