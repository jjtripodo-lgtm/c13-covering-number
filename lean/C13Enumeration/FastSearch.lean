import C13Enumeration.Domains
namespace C13.Enumeration

/-- The matrix can be precomputed and kernel-checked separately from search. -/
def matrixStep (points : List Point) (A B : Point → Point → Nat)
    (remaining : List Point) (f : Point → Point) (a b : Point) : Bool :=
  decide (A a a = B b b) && points.all fun c =>
    if c ∈ remaining then true else decide (A a c = B b (f c))

theorem matrixStep_safe (points : List Point) (A B : Point → Point → Nat)
    (e : Equiv.Perm Point) (h : ∀ a c, A a c = B (e a) (e c))
    (x : Point) (xs : List Point) (f : Point → Point)
    (hf : AgreesOff (x :: xs) f e) :
    matrixStep points A B (x :: xs) f x (e x) = true := by
  unfold matrixStep
  simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  refine ⟨h x x,?_⟩
  intro c hc
  by_cases hmem : c ∈ x :: xs
  · simp [hmem]
  · simp [hmem,hf c hmem,h x c]

def fastCenterSearch (K L : Family Point) (hole c r q : Point) (order : List Point)
    (A B : Point → Point → Nat) : List (Family Point) :=
  if (link K c).card = (link L q).card then
    assignSearch (matrixStep (List.finRange 13) A B)
      (centerFinish K L hole c r q) order (remainingPoints q r) (anchorTable hole r q)
  else []

theorem fastCenterSearch_sound (catalog : Finset (Family Point))
    (K L : Family Point) (hole c r q : Point) (order : List Point)
    (A B : Point → Point → Nat) (hK : K ∈ catalog)
    (P : Family Point) (hP : P ∈ fastCenterSearch K L hole c r q order A B) :
    P ∈ completeDomain catalog hole L r q := by
  unfold fastCenterSearch at hP
  split at hP
  · obtain ⟨f,hf⟩ := assignSearch_sound _ _ _ _ _ P hP
    obtain ⟨hg,hout⟩ := (mem_centerFinish ..).mp hf
    let e : Equiv.Perm Point := Equiv.ofBijective f hg.1
    have he : e hole = q := hg.2.1
    have hc : e c = r := hg.2.2.1
    have hstar : transport e (link K c) = link L q := by
      rw [← mapFamily_equiv]
      exact hg.2.2.2
    apply (mem_completeDomain_iff ..).mpr
    refine ⟨K,hK,e,he,C13.Raw.whole_star_of_punctured_star K L e c r q hc hstar,?_⟩
    rw [← C13.Raw.outside_pencil_from_center K e c r q hc,← mapFamily_equiv]
    exact hout
  · simp at hP

theorem fastCenterSearch_complete (K L : Family Point) (hole c r q : Point)
    (order : List Point) (hn : order.Nodup)
    (horder : ∀ x, x ∈ order ↔ x ≠ hole ∧ x ≠ c)
    (A B : Point → Point → Nat)
    (hA : ∀ a b, A a b = coDegree (link K c) a b)
    (hB : ∀ a b, B a b = coDegree (link L q) a b)
    (e : Equiv.Perm Point) (hhole : e hole = q) (hc : e c = r)
    (hstar : transport e (link K c) = link L q) :
    emitPencil K c q e ∈ fastCenterSearch K L hole c r q order A B := by
  have hcard : (link K c).card = (link L q).card := by
    rw [← hstar,transport_card]
  rw [fastCenterSearch,if_pos hcard]
  apply assignSearch_complete _ _ e e.injective
    (matrixStep_safe _ A B e (fun a b => by rw [hA,hB]; exact coDegree_transport _ _ e hstar a b))
    _ _ _ hn
  · intro x hx
    obtain ⟨hxh,hxc⟩ := (horder x).mp hx
    apply (mem_remainingPoints q r (e x)).mpr
    constructor
    · intro heq
      exact hxh (e.injective (heq.trans hhole.symm))
    · intro heq
      exact hxc (e.injective (heq.trans hc.symm))
  · intro x hx
    by_cases hxh : x = hole
    · subst x
      simp [anchorTable,hhole]
    · have hxc : x = c := by
        by_contra h
        exact hx ((horder x).mpr ⟨hxh,h⟩)
      subst x
      simp [anchorTable,hxh,hc]
  · exact (mem_centerFinish ..).mpr
      ⟨⟨e.bijective,hhole,hc,(mapFamily_equiv e _).trans hstar⟩,rfl⟩
end C13.Enumeration
