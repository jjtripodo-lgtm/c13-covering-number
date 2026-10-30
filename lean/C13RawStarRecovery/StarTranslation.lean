import C13Covering.CatalogReduction

/-! Bridge the whole-star semantic domain to the punctured five-set stars used
by the executable enumerators. This is symbolic completeness of the translation,
not a claim that any serialized raw domain has already been fully enumerated. -/
namespace C13.Raw
open Finset
variable {V : Type*} [DecidableEq V]

theorem transport_outside (e : Equiv.Perm V) (F : Family V) (c : V) :
    transport e (outside F c) = outside (transport e F) (e c) := by
  ext B
  constructor
  · intro hB
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hB
    obtain ⟨hAF,hcA⟩ := mem_outside.mp hA
    exact mem_outside.mpr ⟨mem_image.mpr ⟨A,hAF,rfl⟩,by simpa using hcA⟩
  · intro hB
    obtain ⟨hBF,hcB⟩ := mem_outside.mp hB
    obtain ⟨A,hAF,rfl⟩ := mem_image.mp hBF
    exact mem_image.mpr ⟨A,mem_outside.mpr ⟨hAF,by simpa using hcB⟩,rfl⟩

/-- Removing the known root from its lifted star recovers exactly the five-set
star at q in the root link, provided that root-link blocks avoid the root. -/
theorem erase_crossStar (L : Family V) (r q : V)
    (havoid : ∀ B ∈ L, r ∉ B) :
    (crossStar L r q).image (·.erase r) = link L q := by
  unfold crossStar link
  rw [image_image]
  apply image_congr
  intro B hB
  have hrB := havoid B (mem_star.mp hB).1
  have hrE : r ∉ B.erase q := fun h => hrB (mem_of_mem_erase h)
  exact erase_insert hrE

/-- An entire-star isomorphism is an isomorphism of the punctured stars. -/
theorem punctured_star_of_whole_star (K L : Family V) (e : Equiv.Perm V)
    (c r q : V) (hc : e c = r) (havoid : ∀ B ∈ L, r ∉ B)
    (hstar : star (transport e K) r = crossStar L r q) :
    transport e (link K c) = link L q := by
  rw [transport_link,hc]
  unfold link
  rw [hstar]
  exact erase_crossStar L r q havoid

/-- No source center is omitted: every semantic domain permutation recovers one
as the inverse image of the root, and it differs from the omitted source point. -/
theorem recover_source_center (e : Equiv.Perm V) (hole r q : V)
    (hhole : e hole = q) (hqr : q ≠ r) :
    ∃ c, c ≠ hole ∧ e c = r := by
  refine ⟨e.symm r,?_,e.apply_symm_apply r⟩
  intro h
  have hh := congrArg e h
  rw [e.apply_symm_apply,hhole] at hh
  exact hqr hh.symm

/-- The generator's outside-pencil formula is exactly the semantic formula,
not merely a subset of the true outside pencil. -/
theorem outside_pencil_from_center (K : Family V) (e : Equiv.Perm V)
    (c r q : V) (hc : e c = r) :
    liftAt q (transport e (outside K c)) = liftAt q (outside (transport e K) r) := by
  rw [transport_outside,hc]

/-- Every semantic pencil has a source-center witness and a full punctured-star
bijection before any algorithmic pruning. This is the necessary translation
boundary that a complete executable star enumerator must implement. -/
theorem completeDomain_has_punctured_witness [Fintype V]
    (catalog : Finset (Family V)) (hole : V) (L : Family V) (r q : V)
    (hqr : q ≠ r) (havoid : ∀ B ∈ L, r ∉ B) (P : Family V)
    (hP : P ∈ completeDomain catalog hole L r q) :
    ∃ K ∈ catalog, ∃ c, c ≠ hole ∧ ∃ e : Equiv.Perm V,
      e hole = q ∧ e c = r ∧ transport e (link K c) = link L q ∧
      liftAt q (transport e (outside K c)) = P := by
  obtain ⟨K,hK,e,he,hstar,hout⟩ := (mem_completeDomain_iff ..).mp hP
  obtain ⟨c,hc,her⟩ := recover_source_center e hole r q he hqr
  refine ⟨K,hK,c,hc,e,he,her,punctured_star_of_whole_star K L e c r q her havoid hstar,?_⟩
  rw [outside_pencil_from_center K e c r q her,hout]

theorem lift_link_eq_crossStar (L : Family V) (r q : V) :
    liftAt r (link L q) = crossStar L r q := by
  unfold liftAt link crossStar
  rw [image_image]
  rfl

theorem whole_star_of_punctured_star (K L : Family V) (e : Equiv.Perm V)
    (c r q : V) (hc : e c = r)
    (hstar : transport e (link K c) = link L q) :
    star (transport e K) r = crossStar L r q := by
  have hl : link (transport e K) r = link L q := by
    rw [← hc,← transport_link,hstar]
  rw [← liftAt_link (transport e K) r,hl,lift_link_eq_crossStar]

theorem whole_star_iff_punctured_star (K L : Family V) (e : Equiv.Perm V)
    (c r q : V) (hc : e c = r) (havoid : ∀ B ∈ L, r ∉ B) :
    star (transport e K) r = crossStar L r q ↔
      transport e (link K c) = link L q :=
  ⟨punctured_star_of_whole_star K L e c r q hc havoid,
   whole_star_of_punctured_star K L e c r q hc⟩

end C13.Raw
