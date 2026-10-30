import C13RawStarRecovery.StarTranslation

namespace C13.Raw
variable {V : Type*} [DecidableEq V]

abbrev Punctured (a b : V) := {x : V // x ≠ a ∧ x ≠ b}

def anchoredMap (a b q r : V) (f : Punctured a b ≃ Punctured q r) (x : V) : V :=
  if ha : x = a then q else if hb : x = b then r else (f ⟨x,ha,hb⟩).val

theorem anchoredMap_outside (a b q r : V) (f : Punctured a b ≃ Punctured q r)
    (x : V) (ha : x ≠ a) (hb : x ≠ b) :
    anchoredMap a b q r f x = (f ⟨x,ha,hb⟩).val := by
  simp only [anchoredMap,dif_neg ha,dif_neg hb]

theorem anchoredMap_left_inverse (a b q r : V)
    (hab : a ≠ b) (hqr : q ≠ r) (f : Punctured a b ≃ Punctured q r) :
    Function.LeftInverse (anchoredMap q r a b f.symm) (anchoredMap a b q r f) := by
  intro x
  by_cases ha : x = a
  · subst x
    simp [anchoredMap]
  · by_cases hb : x = b
    · subst x
      simp [anchoredMap,hab.symm,hqr.symm]
    · rw [anchoredMap_outside a b q r f x ha hb]
      rw [anchoredMap_outside q r a b f.symm (f ⟨x,ha,hb⟩).val
        (f ⟨x,ha,hb⟩).property.1 (f ⟨x,ha,hb⟩).property.2]
      exact congrArg Subtype.val (f.symm_apply_apply ⟨x,ha,hb⟩)

/-- Every unrestricted bijection of the doubly punctured universes extends to
an actual ambient permutation sending the two distinguished points as specified. -/
def extendTwoPoints (a b q r : V) (hab : a ≠ b) (hqr : q ≠ r)
    (f : Punctured a b ≃ Punctured q r) : Equiv.Perm V where
  toFun := anchoredMap a b q r f
  invFun := anchoredMap q r a b f.symm
  left_inv := anchoredMap_left_inverse a b q r hab hqr f
  right_inv := by
    intro y
    simpa only [Equiv.symm_symm] using anchoredMap_left_inverse q r a b hqr hab f.symm y

@[simp] theorem extendTwoPoints_first (a b q r : V) (hab : a ≠ b) (hqr : q ≠ r)
    (f : Punctured a b ≃ Punctured q r) : extendTwoPoints a b q r hab hqr f a = q := by
  simp [extendTwoPoints,anchoredMap]

@[simp] theorem extendTwoPoints_second (a b q r : V) (hab : a ≠ b) (hqr : q ≠ r)
    (f : Punctured a b ≃ Punctured q r) : extendTwoPoints a b q r hab hqr f b = r := by
  simp [extendTwoPoints,anchoredMap,hab.symm]

theorem extendTwoPoints_outside (a b q r : V) (hab : a ≠ b) (hqr : q ≠ r)
    (f : Punctured a b ≃ Punctured q r) (x : Punctured a b) :
    extendTwoPoints a b q r hab hqr f x.val = (f x).val := by
  exact anchoredMap_outside a b q r f x.val x.property.1 x.property.2

/-- Restriction of an arbitrary ambient permutation, with no construction-group
or stabilizer restriction beyond its two prescribed images. -/
def restrictTwoPoints (e : Equiv.Perm V) (a b q r : V)
    (ha : e a = q) (hb : e b = r) : Punctured a b ≃ Punctured q r where
  toFun x := ⟨e x.val, by
    constructor
    · intro h
      exact x.property.1 (e.injective (h.trans ha.symm))
    · intro h
      exact x.property.2 (e.injective (h.trans hb.symm))⟩
  invFun y := ⟨e.symm y.val, by
    constructor
    · intro h
      apply y.property.1
      calc
        y.val = e (e.symm y.val) := (e.apply_symm_apply y.val).symm
        _ = e a := congrArg e h
        _ = q := ha
    · intro h
      apply y.property.2
      calc
        y.val = e (e.symm y.val) := (e.apply_symm_apply y.val).symm
        _ = e b := congrArg e h
        _ = r := hb⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val

theorem extend_restrict_two_points (e : Equiv.Perm V) (a b q r : V)
    (hab : a ≠ b) (hqr : q ≠ r) (ha : e a = q) (hb : e b = r) :
    extendTwoPoints a b q r hab hqr (restrictTwoPoints e a b q r ha hb) = e := by
  apply Equiv.ext
  intro x
  by_cases hxa : x = a
  · subst x
    exact (extendTwoPoints_first ..).trans ha.symm
  · by_cases hxb : x = b
    · subst x
      exact (extendTwoPoints_second ..).trans hb.symm
    · exact anchoredMap_outside a b q r (restrictTwoPoints e a b q r ha hb) x hxa hxb

theorem punctured_card_eleven (a b : Point) (hab : a ≠ b) :
    Fintype.card (Punctured a b) = 11 := by
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter (fun x : Point => x ≠ a ∧ x ≠ b)) =
      (Finset.univ.erase a).erase b := by
    ext x
    simp [and_comm]
  rw [he]
  simp [hab.symm]

end C13.Raw
