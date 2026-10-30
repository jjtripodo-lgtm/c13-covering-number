import C13Global.DualBridge
import C13Global.QuadUniverse
import C13RawStarRecovery.StarTranslation
import C13Covering.OrbitAllSources

namespace C13.Global
open Finset C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def ActualObstruction (K : Family Point) (Q : Finset Point) : Prop :=
  ∀ (hclass : ClassifiesMinimumLinks catalog hole)
    (F : Family Point), IsCoverOn univ F 7 4 → link F hole = K →
    (∀ q ∈ Q, degree F q = 15) → (outside F hole).card ≤ 14 → False

theorem degree_transport (e : Equiv.Perm Point) (F : Family Point) (q : Point) :
    degree (transport e F) (e q) = degree F q := by
  rw [← link_card,← transport_link,transport_card,link_card]

theorem obstruction_transport (K : Family Point) (Q Q' : Finset Point)
    (e : Equiv.Perm Point) (eh : e hole = hole) (eK : transport e K = K)
    (eQ : Q.map e.toEmbedding = Q') (h : ActualObstruction K Q) :
    ActualObstruction K Q' := by
  intro hc F hF hroot hmin hout
  apply h hc (transport e.symm F) (transport_cover e.symm hF)
  · have eh' : e.symm hole = hole := by
      apply e.injective
      simpa only [Equiv.apply_symm_apply] using eh.symm
    rw [← eh',← transport_link,hroot]
    calc
      transport e.symm K = transport e.symm (transport e K) := congrArg (transport e.symm) eK.symm
      _ = K := transport_inverse e K
  · intro q hq
    have hmem : e q ∈ Q' := by rw [← eQ]; exact mem_map.mpr ⟨q,hq,rfl⟩
    have hh := degree_transport e.symm F (e q)
    simpa using hh.trans (hmin _ hmem)
  · have eh' : e.symm hole = hole := by
      apply e.injective
      simpa only [Equiv.apply_symm_apply] using eh.symm
    rw [← eh',← C13.Raw.transport_outside,transport_card]
    exact hout

def quadFinsets : List (Finset Point) := quadPoints.map List.toFinset

theorem quadFinsets_complete : quadFinsets.toFinset =
    (univ.erase hole).powersetCard 4 := by
  have he : quadFinsets = quadCodes.map C13.Enumeration.decodeTyped := by decide +kernel
  rw [he]
  exact quadCodes_complete

theorem quadPoints_complete (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ∃ qs ∈ quadPoints, qs.toFinset = Q := by
  rw [← quadFinsets_complete] at hQ
  exact List.mem_map.mp (List.mem_toFinset.mp hQ)

theorem empty_obstruction_mono (K : Family Point) (emptyCases : List EmptyCase)
    (hempty : ∀ c ∈ emptyCases, ActualObstruction K c.1.toFinset)
    (points : List Point) (checked : emptyCoversB emptyCases points = true) :
    ActualObstruction K points.toFinset := by
  obtain ⟨c,hc,hsub⟩ := emptyCovers_sound emptyCases points checked
  intro hclass F hcover hroot hmin hout
  exact hempty c hc hclass F hcover hroot
    (fun q hq => hmin q (List.mem_toFinset.mpr (hsub q (List.mem_toFinset.mp hq)))) hout

theorem class_census (K : Family Point) (emptyCases : List EmptyCase)
    (hempty : ∀ c ∈ emptyCases, ActualObstruction K c.1.toFinset)
    (dualQuads : List (Finset Point))
    (hdual : ∀ Q ∈ dualQuads, ActualObstruction K Q)
    (checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
      decide (qs.toFinset ∈ dualQuads)) = true)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction K Q := by
  obtain ⟨qs,hqs,rfl⟩ := quadPoints_complete Q hQ
  have hh := List.all_eq_true.mp checked qs hqs
  simp only [Bool.or_eq_true_iff] at hh
  rcases hh with he | hd
  · exact empty_obstruction_mono K emptyCases hempty qs he
  · exact hdual _ (of_decide_eq_true hd)

end C13.Global
