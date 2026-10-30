import C13Global.LowerBoundCore
namespace C13.Global
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Every block has a triple which appears in no other block. -/
def PrivateTriples (K : Family Point) : Prop :=
  ∀ B ∈ K, ∃ T : Finset Point, T ⊆ B ∧ T.card = 3 ∧
    ∀ C ∈ K, T ⊆ C → C = B

def privateTripleCheckB (root : List Code) (witnesses : List (Code × Code)) : Bool :=
  root.all fun b => witnesses.any fun p => decide (p.1 = b) &&
    decide ((decodeTyped p.2).card = 3) && subsetB p.2 b &&
    root.all (fun c => !(subsetB p.2 c) || decide (c = b))

theorem privateTripleCheck_sound (root : List Code) (witnesses : List (Code × Code))
    (checked : privateTripleCheckB root witnesses = true) : PrivateTriples (decodeSource root) := by
  intro B hB
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hB)
  obtain ⟨p,_,hp⟩ := List.any_eq_true.mp (List.all_eq_true.mp checked b hb)
  have hh : p.1 = b ∧ (decodeTyped p.2).card = 3 ∧ subsetB p.2 b = true ∧
      root.all (fun c => !(subsetB p.2 c) || decide (c = b)) = true := by
    simpa only [Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hp
  refine ⟨decodeTyped p.2,(C13.Enumeration.Census.subsetB_iff _ _).mp hh.2.2.1,hh.2.1,?_⟩
  intro C hC ht
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hC)
  have hx := List.all_eq_true.mp hh.2.2.2 c hc
  have hs : subsetB p.2 c = true := (C13.Enumeration.Census.subsetB_iff _ _).mpr ht
  have he : c = b := by simpa [hs] using hx
  subst c
  rfl

theorem privateTriples_transport (K : Family Point) (e : Equiv.Perm Point)
    (h : PrivateTriples K) : PrivateTriples (transport e K) := by
  intro B hB
  obtain ⟨A,hA,rfl⟩ := mem_image.mp hB
  obtain ⟨T,hTA,hT,hunique⟩ := h A hA
  refine ⟨T.map e.toEmbedding,(map_subset_map (f := e.toEmbedding)).mpr hTA,by simpa using hT,?_⟩
  intro C hC hTC
  obtain ⟨D,hD,rfl⟩ := mem_image.mp hC
  have hDA := hunique D hD ((map_subset_map (f := e.toEmbedding)).mp hTC)
  exact congrArg (fun X : Finset Point => X.map e.toEmbedding) hDA

theorem privateTriples_subcover_eq (U : Finset Point) (L K : Family Point)
    (hL : IsCoverOn U L 6 3) (hKU : ∀ B ∈ K, B ⊆ U)
    (hLK : L ⊆ K) (hprivate : PrivateTriples K) : L = K := by
  apply subset_antisymm hLK
  intro B hB
  obtain ⟨T,hTB,hT,hunique⟩ := hprivate B hB
  obtain ⟨C,hC,hTC⟩ := hL.2 T (hTB.trans (hKU B hB)) hT
  exact (hunique C (hLK hC) hTC) ▸ hC

/-- The classification predicate quantifies over every size-15 cover. If its
catalog is block-irredundant, padding forces the minimum bound. Thus this is
not an independent proof of the published classification theorem. -/
theorem minimum_bound_of_classified_private_triples
    (hclass : ClassifiesMinimumLinks catalog hole)
    (hprivate : ∀ K ∈ catalog, PrivateTriples K) : PublishedMinimumBound Point := by
  intro U L hU hL
  by_contra hn
  have hsmall : L.card ≤ 15 := by omega
  have hsub : L ⊆ U.powersetCard 6 := by
    intro B hB
    exact mem_powersetCard.mpr (hL.1 B hB)
  have hcapacity : 15 ≤ (U.powersetCard 6).card := by
    rw [card_powersetCard,hU]
    decide
  obtain ⟨G,hLG,hGU,hG15⟩ := exists_subsuperset_card_eq hsub hsmall hcapacity
  have hG : IsCoverOn U G 6 3 :=
    hL.mono_family hLG (fun B hB => mem_powersetCard.mp (hGU hB))
  obtain ⟨q,hq⟩ : ∃ q : Point, q ∉ U := by
    by_contra h
    have hu : (univ : Finset Point) ⊆ U := by
      intro q _
      by_contra hq
      exact h ⟨q,hq⟩
    have hc := card_le_card hu
    simp only [card_univ,Fintype.card_fin,hU] at hc
    omega
  have hUeq : U = univ.erase q := by
    apply eq_of_subset_of_card_le
    · intro x hx
      exact mem_erase.mpr ⟨by intro he; subst x; exact hq hx,mem_univ _⟩
    · simp only [card_erase_of_mem (mem_univ q),card_univ,Fintype.card_fin,hU]
      omega
  obtain ⟨K,hK,e,_,he⟩ := hclass q G (by rw [← hUeq]; exact hG) hG15
  have hgprivate : PrivateTriples G := he ▸ privateTriples_transport K e (hprivate K hK)
  have hLG_eq := privateTriples_subcover_eq U L G hL (fun B hB => (hG.1 B hB).1) hLG hgprivate
  have hL15 : L.card = 15 := by rw [hLG_eq,hG15]
  omega
end C13.Global
