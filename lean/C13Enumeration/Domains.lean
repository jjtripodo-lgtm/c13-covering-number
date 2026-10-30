import C13Enumeration.StarPrune
import Mathlib.Data.List.FinRange

namespace C13.Enumeration
open Finset

/-- Exact leaf predicate: bijective on the entire ambient universe, two
prescribed images, and equality of the full punctured stars. -/
def GoodMap (K L : Family Point) (hole c r q : Point) (f : Point → Point) : Prop :=
  Function.Bijective f ∧ f hole = q ∧ f c = r ∧ mapFamily f (link K c) = link L q
instance (K L : Family Point) (hole c r q : Point) (f : Point → Point) :
    Decidable (GoodMap K L hole c r q f) := inferInstanceAs (Decidable
      (Function.Bijective f ∧ f hole = q ∧ f c = r ∧ mapFamily f (link K c) = link L q))

def emitPencil (K : Family Point) (c q : Point) (f : Point → Point) : Family Point :=
  liftAt q (mapFamily f (outside K c))

def centerFinish (K L : Family Point) (hole c r q : Point) (f : Point → Point) : List (Family Point) :=
  if GoodMap K L hole c r q f then [emitPencil K c q f] else []

theorem mem_centerFinish (K L : Family Point) (hole c r q : Point)
    (f : Point → Point) (P : Family Point) :
    P ∈ centerFinish K L hole c r q f ↔
      GoodMap K L hole c r q f ∧ emitPencil K c q f = P := by
  unfold centerFinish
  by_cases h : GoodMap K L hole c r q f
  · rw [if_pos h]
    simp only [List.mem_singleton]
    exact ⟨fun hp => ⟨h,hp.symm⟩,fun hp => hp.2.symm⟩
  · rw [if_neg h]
    simp only [List.not_mem_nil,false_iff,not_and]
    exact fun hg => (h hg).elim

/-- All points are listed. In particular no isolated incidence fiber disappears. -/
def remainingPoints (a b : Point) : List Point :=
  (List.finRange 13).filter fun x => decide (x ≠ a ∧ x ≠ b)

@[simp] theorem mem_remainingPoints (a b x : Point) :
    x ∈ remainingPoints a b ↔ x ≠ a ∧ x ≠ b := by
  simp [remainingPoints]

theorem remainingPoints_nodup (a b : Point) : (remainingPoints a b).Nodup := by
  exact (List.nodup_finRange 13).filter _

def anchorTable (hole r q : Point) (x : Point) : Point := if x = hole then q else r

/-- The order is an optimization parameter; the completeness theorem below
requires it to contain exactly the doubly punctured source universe. -/
def centerSearch (K L : Family Point) (hole c r q : Point) (order : List Point) :
    List (Family Point) :=
  search (pairPrune (link K c) (link L q)) (centerFinish K L hole c r q)
    order (remainingPoints q r) (anchorTable hole r q)

theorem centerSearch_sound (catalog : Finset (Family Point))
    (K L : Family Point) (hole c r q : Point) (order : List Point) (hK : K ∈ catalog)
    (P : Family Point) (hP : P ∈ centerSearch K L hole c r q order) :
    P ∈ completeDomain catalog hole L r q := by
  obtain ⟨f,hf⟩ := search_sound _ _ _ _ _ P hP
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

theorem centerSearch_complete (K L : Family Point) (hole c r q : Point)
    (order : List Point) (hn : order.Nodup)
    (horder : ∀ x, x ∈ order ↔ x ≠ hole ∧ x ≠ c)
    (e : Equiv.Perm Point) (hhole : e hole = q) (hc : e c = r)
    (hstar : transport e (link K c) = link L q) :
    emitPencil K c q e ∈ centerSearch K L hole c r q order := by
  apply search_complete _ _ e e.injective
    (pairPrune_safe (link K c) (link L q) e hstar) _ _ _ hn
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

/-- Every catalog entry and every source center is included explicitly. -/
def enumerateDomain (catalog : List (Family Point)) (hole : Point) (L : Family Point) (r q : Point) :
    List (Family Point) :=
  catalog.flatMap fun K =>
    ((List.finRange 13).filter fun x => x ≠ hole).flatMap fun c =>
      centerSearch K L hole c r q (remainingPoints hole c)

/-- Exact semantic equality for the executable pruned generator. This is a
symbolic completeness result, not a claim that a supplied literal row table has
already been checked equal to this generator's output. -/
theorem enumerateDomain_eq_completeDomain (catalog : List (Family Point))
    (hole : Point) (L : Family Point) (r q : Point) (hqr : q ≠ r)
    (havoid : ∀ B ∈ L, r ∉ B) :
    (enumerateDomain catalog hole L r q).toFinset =
      completeDomain catalog.toFinset hole L r q := by
  ext P
  simp only [List.mem_toFinset]
  constructor
  · intro hP
    obtain ⟨K,hK,hP⟩ := List.mem_flatMap.mp hP
    obtain ⟨c,hc,hP⟩ := List.mem_flatMap.mp hP
    exact centerSearch_sound catalog.toFinset K L hole c r q _
      (List.mem_toFinset.mpr hK) P hP
  · intro hP
    obtain ⟨K,hK,c,hc,e,he,hce,hstar,hout⟩ :=
      C13.Raw.completeDomain_has_punctured_witness catalog.toFinset hole L r q hqr havoid P hP
    unfold enumerateDomain
    apply List.mem_flatMap.mpr
    refine ⟨K,List.mem_toFinset.mp hK,List.mem_flatMap.mpr ?_⟩
    refine ⟨c,by simp [hc],?_⟩
    have h := centerSearch_complete K L hole c r q (remainingPoints hole c)
      (remainingPoints_nodup hole c) (fun x => mem_remainingPoints hole c x) e he hce hstar
    have hemit : emitPencil K c q e = P := by
      unfold emitPencil
      rw [mapFamily_equiv]
      exact hout
    exact hemit ▸ h
end C13.Enumeration
