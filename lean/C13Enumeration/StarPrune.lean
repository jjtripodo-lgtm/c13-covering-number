import C13Enumeration.Search

namespace C13.Enumeration
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Repeated arguments give the vertex degree; distinct arguments give the
number of star blocks containing the pair. -/
def coDegree (S : Family V) (a b : V) : Nat := (star (star S a) b).card

theorem coDegree_transport (S T : Family V) (e : Equiv.Perm V)
    (he : transport e S = T) (a b : V) :
    coDegree S a b = coDegree T (e a) (e b) := by
  unfold coDegree
  rw [← he,← transport_star,← transport_star,transport_card]

/-- Exact pair-incidence pruning on the assigned complement. This tests all
ambient points rather than only the union of the star's blocks. -/
def pairPrune (S T : Family V) (remaining : List V) (f : V → V) : Bool :=
  decide (∀ a : V, a ∉ remaining → ∀ b : V, b ∉ remaining →
    coDegree S a b = coDegree T (f a) (f b))

theorem pairPrune_safe (S T : Family V) (e : Equiv.Perm V)
    (he : transport e S = T) (remaining : List V) (f : V → V)
    (hf : AgreesOff remaining f e) : pairPrune S T remaining f = true := by
  simp only [pairPrune,decide_eq_true_eq]
  intro a ha b hb
  rw [hf a ha,hf b hb]
  exact coDegree_transport S T e he a b

/-- Extensional transport computable from a plain finite map. -/
def mapFamily (f : V → V) (S : Family V) : Family V :=
  S.image fun B => B.image f

theorem mapFamily_equiv (e : Equiv.Perm V) (S : Family V) :
    mapFamily e S = transport e S := by
  unfold mapFamily transport
  apply image_congr
  intro B _
  exact (Finset.map_eq_image e.toEmbedding B).symm

/-- Every rejected leaf fails a stated semantic requirement. -/
def starFinish (S T : Family V) (emit : (V → V) → Family V)
    (f : V → V) : List (Family V) :=
  if Function.Bijective f ∧ mapFamily f S = T then [emit f] else []

theorem mem_starFinish (S T : Family V) (emit : (V → V) → Family V)
    (f : V → V) (P : Family V) :
    P ∈ starFinish S T emit f ↔
    Function.Bijective f ∧ mapFamily f S = T ∧ emit f = P := by
  simp only [starFinish]
  by_cases h : Function.Bijective f ∧ mapFamily f S = T
  · rw [if_pos h]
    simp only [List.mem_singleton]
    exact ⟨fun hp => ⟨h.1,h.2,hp.symm⟩,fun hp => hp.2.2.symm⟩
  · rw [if_neg h]
    simp only [List.not_mem_nil, false_iff, not_and]
    intro hb hs
    exact (h ⟨hb,hs⟩).elim

theorem starFinish_complete (S T : Family V) (emit : (V → V) → Family V)
    (e : Equiv.Perm V) (he : transport e S = T) :
    emit e ∈ starFinish S T emit e := by
  exact (mem_starFinish ..).mpr ⟨e.bijective,(mapFamily_equiv e S).trans he,rfl⟩

end C13.Enumeration
