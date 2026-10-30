import C13Covering.Reduction
import Mathlib.Data.Fintype.Perm

/-! Complete semantic pencil domains, using every ambient permutation.
This construction is mathematically finite but is not the optimized Python
star-isomorphism enumerator. Equality with serialized executable domains is a
separate obligation, deliberately not presumed by any theorem below. -/
namespace C13
open Finset
variable {V : Type*} [DecidableEq V]

def liftAt (q : V) (L : Family V) : Family V := L.image (insert q)

def crossStar (L : Family V) (r q : V) : Family V :=
  (star L q).image (fun B => insert r (B.erase q))

def transport (e : Equiv.Perm V) (F : Family V) : Family V :=
  F.image (Finset.map e.toEmbedding)

@[simp] theorem liftAt_link (F : Family V) (q : V) : liftAt q (link F q) = star F q := by
  unfold liftAt link
  rw [image_image]
  calc
    _ = (star F q).image id := by
      apply image_congr
      intro B hB
      exact insert_erase (mem_star.mp hB).2
    _ = _ := image_id

theorem pencil_from_link (F : Family V) {r q : V} (hqr : q ≠ r) :
    pencil F r q = liftAt q (outside (link F q) r) := by
  ext B
  constructor
  · intro hB
    obtain ⟨hBF,hrB,hqB⟩ := mem_pencil.mp hB
    refine mem_image.mpr ⟨B.erase q, mem_outside.mpr ⟨?_,?_⟩,insert_erase hqB⟩
    · exact mem_image.mpr ⟨B,mem_star.mpr ⟨hBF,hqB⟩,rfl⟩
    · exact fun h => hrB (mem_of_mem_erase h)
  · intro hB
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hB
    obtain ⟨hAL,hrA⟩ := mem_outside.mp hA
    obtain ⟨B,hBstar,rfl⟩ := mem_image.mp hAL
    obtain ⟨hBF,hqB⟩ := mem_star.mp hBstar
    rw [insert_erase hqB]
    refine mem_pencil.mpr ⟨hBF,?_,hqB⟩
    intro hrB
    exact hrA (mem_erase.mpr ⟨Ne.symm hqr,hrB⟩)

theorem star_link_crossStar (F : Family V) {r q : V} (hqr : q ≠ r) :
    star (link F q) r = crossStar (link F r) r q := by
  ext A
  constructor
  · intro hA
    obtain ⟨hAL,hrA⟩ := mem_star.mp hA
    obtain ⟨B,hBstar,rfl⟩ := mem_image.mp hAL
    obtain ⟨hBF,hqB⟩ := mem_star.mp hBstar
    have hrB := mem_of_mem_erase hrA
    refine mem_image.mpr ⟨B.erase r,mem_star.mpr ⟨?_,?_⟩,?_⟩
    · exact mem_image.mpr ⟨B,mem_star.mpr ⟨hBF,hrB⟩,rfl⟩
    · exact mem_erase.mpr ⟨hqr,hqB⟩
    · rw [erase_right_comm, insert_erase hrA]
  · intro hA
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hA
    obtain ⟨hBL,hqB⟩ := mem_star.mp hB
    obtain ⟨C,hC,rfl⟩ := mem_image.mp hBL
    obtain ⟨hCF,hrC⟩ := mem_star.mp hC
    have hqC := mem_of_mem_erase hqB
    have hrCq : r ∈ C.erase q := mem_erase.mpr ⟨Ne.symm hqr,hrC⟩
    rw [erase_right_comm,insert_erase hrCq]
    exact mem_star.mpr ⟨mem_image.mpr ⟨C,mem_star.mpr ⟨hCF,hqC⟩,rfl⟩,hrCq⟩

/-- Every minimum link is isomorphic to some member of the specified family.
When instantiated with the literal Figure-1/Figure-6 source universe, this is
the external published classification. For the compressed 68-member catalog,
it additionally needs the separate source-coverage theorem. -/
def ClassifiesMinimumLinks [Fintype V] (catalog : Finset (Family V)) (hole : V) : Prop :=
  ∀ q (L : Family V), IsCoverOn (univ.erase q) L 6 3 → L.card = 15 →
    ∃ K ∈ catalog, ∃ e : Equiv.Perm V, e hole = q ∧ transport e K = L

/-- Enumerate all classified sources and every permutation matching the entire
known star. Fixing the omitted source point to q leaves unrestricted maps of
the other twelve points; the source center is the inverse image of r. Thus no
construction group, point stabilizer, or ordinary-family-only restriction is
part of this semantic domain. -/
def completeDomain [Fintype V] (catalog : Finset (Family V)) (hole : V)
    (L : Family V) (r q : V) : Finset (Family V) :=
  catalog.biUnion fun K =>
    ((univ : Finset (Equiv.Perm V)).filter fun e =>
      e hole = q ∧ star (transport e K) r = crossStar L r q).image
      (fun e => liftAt q (outside (transport e K) r))

theorem mem_completeDomain_iff [Fintype V] (catalog : Finset (Family V)) (hole : V)
    (L : Family V) (r q : V) (P : Family V) :
    P ∈ completeDomain catalog hole L r q ↔
      ∃ K ∈ catalog, ∃ e : Equiv.Perm V,
        e hole = q ∧ star (transport e K) r = crossStar L r q ∧
        liftAt q (outside (transport e K) r) = P := by
  simp [completeDomain, and_assoc]

theorem actual_pencil_mem_completeDomain (catalog : Finset (Family Point)) (hole : Point)
    (hclass : ClassifiesMinimumLinks catalog hole) (F : Family Point)
    (hcover : IsCoverOn univ F 7 4) {r q : Point} (hqr : q ≠ r)
    (hq : degree F q = 15) :
    pencil F r q ∈ completeDomain catalog hole (link F r) r q := by
  obtain ⟨K,hK,e,he,hL⟩ := hclass q (link F q)
    (link_isCoverOn hcover (mem_univ q)) (by rw [link_card,hq])
  apply (mem_completeDomain_iff ..).mpr
  refine ⟨K,hK,e,he,?_,?_⟩
  · rw [hL]
    exact star_link_crossStar F hqr
  · rw [hL]
    exact (pencil_from_link F hqr).symm

/-- Full four-way necessary condition from a hypothetical cover. The first
premise is the published minimum bound; the second is the complete published
classification transported through an explicitly identified catalog. -/
theorem cover29_classified_reduction (catalog : Finset (Family Point)) (hole : Point)
    (hpub : PublishedMinimumBound Point) (hclass : ClassifiesMinimumLinks catalog hole)
    (F : Family Point) (hcover : IsCoverOn univ F 7 4) (h29 : F.card = 29) :
    ∃ (r : Point) (Q : Finset Point) (P : Point → Family Point),
      Q.card = 4 ∧ r ∉ Q ∧ degree F r = 15 ∧
      (∀ q ∈ Q, P q ∈ completeDomain catalog hole (link F r) r q) ∧
      (∀ q ∈ Q, ∀ s ∈ Q, star (P q) s = star (P s) q) ∧
      (Q.biUnion P).card ≤ 14 := by
  obtain ⟨r,Q,hQ,hrQ,hr,hq,ho,hpair,hunion⟩ := cover29_reduction F hcover h29 hpub
  refine ⟨r,Q,pencil F r,hQ,hrQ,hr,?_,hpair,hunion⟩
  intro q hqQ
  exact actual_pencil_mem_completeDomain catalog hole hclass F hcover
    (by intro h; subst q; exact hrQ hqQ) (hq q hqQ)

end C13
