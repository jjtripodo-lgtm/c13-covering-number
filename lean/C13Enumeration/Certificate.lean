import C13Enumeration.Signatures
namespace C13.Enumeration

/-- A compositional search certificate. The allowed child list is only an
overapproximation; its coverage is checked at every visited prefix. -/
theorem assignSearch_bound_cons {R : Family Point → Prop}
    (step : List Point → (Point → Point) → Point → Point → Bool)
    (finish : (Point → Point) → List (Family Point))
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

theorem list_all_eq_bound (xs : List (Family Point)) (P : Family Point)
    (h : (xs.all fun Q => decide (Q = P)) = true) : ∀ Q ∈ xs, Q = P := by
  intro Q hQ
  exact of_decide_eq_true ((List.all_eq_true.mp h) Q hQ)

/-- A proved full-search bound closes the semantic source-center obligation. -/
theorem pencil_eq_of_search_bound (K L : Family Point) (hole c r q : Point)
    (order : List Point) (hn : order.Nodup)
    (horder : ∀ x, x ∈ order ↔ x ≠ hole ∧ x ≠ c)
    (A B : Point → Point → Nat)
    (hA : ∀ a b, A a b = coDegree (link K c) a b)
    (hB : ∀ a b, B a b = coDegree (link L q) a b)
    (P : Family Point)
    (hbound : ∀ Q ∈ assignSearch (matrixStep (List.finRange 13) A B)
        (centerFinish K L hole c r q) order (remainingPoints q r) (anchorTable hole r q), Q = P)
    (e : Equiv.Perm Point) (hhole : e hole = q) (hc : e c = r)
    (hstar : transport e (link K c) = link L q) : emitPencil K c q e = P := by
  apply hbound
  have h := fastCenterSearch_complete K L hole c r q order hn horder A B hA hB e hhole hc hstar
  unfold fastCenterSearch at h
  split at h
  · exact h
  · simp at h
end C13.Enumeration
