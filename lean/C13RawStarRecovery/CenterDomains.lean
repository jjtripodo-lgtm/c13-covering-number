import C13RawStarRecovery.TwoPointBijections

namespace C13.Raw
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A finite semantic generator with all source centers and ALL bijections of
the two doubly punctured point universes. In the C13 instance those universes
have exactly eleven points, including points isolated in the star. This is a
specification; this file does not execute a factorial enumeration. -/
def puncturedDomain (catalog : Finset (Family V)) (hole : V) (L : Family V)
    (r q : V) (hqr : q ≠ r) : Finset (Family V) :=
  catalog.biUnion fun K =>
    (univ : Finset {c : V // c ≠ hole}).biUnion fun c =>
      ((univ : Finset (Punctured hole c.val ≃ Punctured q r)).filter fun f =>
        transport (extendTwoPoints hole c.val q r c.property.symm hqr f) (link K c.val) =
          link L q).image fun f =>
            liftAt q (transport (extendTwoPoints hole c.val q r c.property.symm hqr f)
              (outside K c.val))

theorem mem_puncturedDomain_iff (catalog : Finset (Family V)) (hole : V) (L : Family V)
    (r q : V) (hqr : q ≠ r) (P : Family V) :
    P ∈ puncturedDomain catalog hole L r q hqr ↔
      ∃ K ∈ catalog, ∃ c : {c : V // c ≠ hole},
        ∃ f : Punctured hole c.val ≃ Punctured q r,
          transport (extendTwoPoints hole c.val q r c.property.symm hqr f) (link K c.val) =
            link L q ∧
          liftAt q (transport (extendTwoPoints hole c.val q r c.property.symm hqr f)
            (outside K c.val)) = P := by
  simp [puncturedDomain]

/-- Exact equivalence, rather than a one-way subset argument: the complete
ambient-permutation domain equals the all-center, unrestricted punctured-star
bijection domain. No special family, construction subgroup or favorable root
is substituted for the whole catalog. -/
theorem completeDomain_eq_puncturedDomain (catalog : Finset (Family V)) (hole : V)
    (L : Family V) (r q : V) (hqr : q ≠ r) (havoid : ∀ B ∈ L, r ∉ B) :
    completeDomain catalog hole L r q = puncturedDomain catalog hole L r q hqr := by
  ext P
  constructor
  · intro hP
    obtain ⟨K,hK,c,hc,e,he,hce,hstar,hout⟩ :=
      completeDomain_has_punctured_witness catalog hole L r q hqr havoid P hP
    let f := restrictTwoPoints e hole c q r he hce
    have hext : extendTwoPoints hole c q r hc.symm hqr f = e :=
      extend_restrict_two_points e hole c q r hc.symm hqr he hce
    apply (mem_puncturedDomain_iff ..).mpr
    refine ⟨K,hK,⟨c,hc⟩,f,?_,?_⟩
    · exact hext ▸ hstar
    · exact hext ▸ hout
  · intro hP
    obtain ⟨K,hK,c,f,hstar,hout⟩ := (mem_puncturedDomain_iff ..).mp hP
    let e := extendTwoPoints hole c.val q r c.property.symm hqr f
    have he : e hole = q := extendTwoPoints_first ..
    have hc : e c.val = r := extendTwoPoints_second ..
    apply (mem_completeDomain_iff ..).mpr
    refine ⟨K,hK,e,he,whole_star_of_punctured_star K L e c.val r q hc hstar,?_⟩
    rw [← outside_pencil_from_center K e c.val r q hc]
    exact hout

end C13.Raw
