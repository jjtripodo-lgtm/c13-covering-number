import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum

/-! Literal finite-cover reduction for C(13,7,4). The published minimum-link
bound and classification are theorem parameters, never added axioms.
No executable-domain exhaustiveness or finite obstruction is assumed silently. -/
namespace C13
open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

abbrev Family (V : Type*) := Finset (Finset V)

def IsCoverOn (U : Finset V) (F : Family V) (k t : ℕ) : Prop :=
  (∀ B ∈ F, B ⊆ U ∧ B.card = k) ∧
  ∀ T ⊆ U, T.card = t → ∃ B ∈ F, T ⊆ B

def star (F : Family V) (q : V) : Family V := F.filter (q ∈ ·)
def outside (F : Family V) (q : V) : Family V := F.filter (q ∉ ·)
def degree (F : Family V) (q : V) : ℕ := (star F q).card
def link (F : Family V) (q : V) : Family V := (star F q).image (·.erase q)
def pencil (F : Family V) (r q : V) : Family V := star (outside F r) q

@[simp] theorem mem_star {F : Family V} {q : V} {B : Finset V} :
    B ∈ star F q ↔ B ∈ F ∧ q ∈ B := by simp [star]
@[simp] theorem mem_outside {F : Family V} {q : V} {B : Finset V} :
    B ∈ outside F q ↔ B ∈ F ∧ q ∉ B := by simp [outside]
@[simp] theorem mem_pencil {F : Family V} {r q : V} {B : Finset V} :
    B ∈ pencil F r q ↔ B ∈ F ∧ r ∉ B ∧ q ∈ B := by simp [pencil, and_assoc]

theorem link_card (F : Family V) (q : V) : (link F q).card = degree F q := by
  apply (Finset.card_image_iff).2
  intro A hA B hB h
  have ha := (mem_star.mp hA).2
  have hb := (mem_star.mp hB).2
  have := congrArg (insert q) h
  simpa [insert_erase ha, insert_erase hb] using this

theorem link_isCoverOn {U : Finset V} {F : Family V} {q : V} {k t : ℕ}
    (h : IsCoverOn U F (k+1) (t+1)) (hq : q ∈ U) :
    IsCoverOn (U.erase q) (link F q) k t := by
  constructor
  · intro B hB
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨hAF,hqA⟩ := mem_star.mp hA
    obtain ⟨hAU,hAk⟩ := h.1 A hAF
    constructor
    · exact erase_subset_erase q hAU
    · rw [card_erase_of_mem hqA, hAk]
      omega
  · intro T hTU hT
    have hqT : q ∉ T := by
      intro hqT
      exact (mem_erase.mp (hTU hqT)).1 rfl
    have hiU : insert q T ⊆ U := insert_subset hq (Subset.trans hTU (erase_subset _ _))
    have hiT : (insert q T).card = t+1 := by rw [card_insert_of_notMem hqT, hT]
    obtain ⟨B,hBF,hTB⟩ := h.2 (insert q T) hiU hiT
    refine ⟨B.erase q, mem_image.mpr ⟨B, mem_star.mpr ⟨hBF,hTB (mem_insert_self _ _)⟩,rfl⟩, ?_⟩
    intro x hx
    exact mem_erase.mpr ⟨by intro he; subst x; exact hqT hx, hTB (mem_insert_of_mem hx)⟩

theorem sum_degrees [Fintype V] (F : Family V) :
    ∑ q : V, degree F q = ∑ B ∈ F, B.card := by
  simp only [degree, star, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro B hB
  simp

theorem sum_degrees_uniform [Fintype V] (F : Family V) (k : ℕ)
    (h : ∀ B ∈ F, B.card = k) : ∑ q : V, degree F q = F.card * k := by
  rw [sum_degrees]
  calc
    _ = ∑ _B ∈ F, k := sum_congr rfl h
    _ = F.card * k := by simp

theorem degree_add_outside (F : Family V) (r : V) :
    degree F r + (outside F r).card = F.card :=
  card_filter_add_card_filter_not (r ∈ ·)

theorem pencil_pair_agreement (F : Family V) (r q s : V) :
    star (pencil F r q) s = star (pencil F r s) q := by
  ext B
  simp [and_assoc, and_left_comm, and_comm]

theorem pencil_union_subset (F : Family V) (r : V) (Q : Finset V) :
    Q.biUnion (pencil F r) ⊆ outside F r := by
  intro B hB
  obtain ⟨q,_,h⟩ := mem_biUnion.mp hB
  exact (mem_star.mp h).1

theorem pencil_union_budget (F : Family V) (r : V) (Q : Finset V) (n : ℕ)
    (h : (outside F r).card ≤ n) : (Q.biUnion (pencil F r)).card ≤ n :=
  (card_le_card (pencil_union_subset F r Q)).trans h

/-- The lower-dimensional result from Gordon–Patashnik–Petro–Taylor (1995),
Theorem 4.4, represented on arbitrary twelve-point subsets of this ambient set.
It is not proved or declared as an axiom in this development. -/
def PublishedMinimumBound (V : Type*) [DecidableEq V] : Prop :=
  ∀ (U : Finset V) (L : Family V), U.card = 12 → IsCoverOn U L 6 3 → 15 ≤ L.card

abbrev Point := Fin 13

theorem all_degrees_ge15 (F : Family Point)
    (hcover : IsCoverOn univ F 7 4) (hpub : PublishedMinimumBound Point) :
    ∀ q, 15 ≤ degree F q := by
  intro q
  rw [← link_card]
  exact hpub (univ.erase q) (link F q) (by simp) (link_isCoverOn hcover (mem_univ q))

/-- A purely numerical incidence lemma. -/
theorem five_minimum_degrees (d : Point → ℕ)
    (hlower : ∀ q, 15 ≤ d q) (hsum : ∑ q, d q = 203) :
    5 ≤ (univ.filter (d · = 15)).card := by
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset Point)) (d · = 15)
  have hle : ∑ q : Point, (if d q = 15 then 15 else 16) ≤ ∑ q : Point, d q := by
    apply sum_le_sum
    intro q _
    split_ifs with h
    · exact hlower q
    · have := hlower q; omega
  have hcount : (∑ q : Point, (if d q = 15 then 15 else 16)) =
      (univ.filter (d · = 15)).card * 15 + (univ.filter (fun q => ¬ d q = 15)).card * 16 := by
    rw [← sum_filter_add_sum_filter_not (s := univ) (p := (d · = 15))]
    congr 1
    · calc
        _ = ∑ _q ∈ univ.filter (d · = 15), 15 := by
          apply sum_congr rfl
          intro q hq
          simp only [(mem_filter.mp hq).2, if_true]
        _ = _ := by simp
    · calc
        _ = ∑ _q ∈ univ.filter (fun q => ¬d q = 15), 16 := by
          apply sum_congr rfl
          intro q hq
          simp only [(mem_filter.mp hq).2, if_false]
        _ = _ := by simp
  rw [hcount, hsum] at hle
  simp only [card_univ, Fintype.card_fin] at hsplit
  omega

/-- A real 29-block cover supplies a root and four further distinct minimum
points. Their complete outside pencils fit in fourteen literal blocks. -/
theorem cover29_reduction (F : Family Point)
    (hcover : IsCoverOn univ F 7 4) (h29 : F.card = 29)
    (hpub : PublishedMinimumBound Point) :
    ∃ (r : Point) (Q : Finset Point), Q.card = 4 ∧ r ∉ Q ∧ degree F r = 15 ∧
      (∀ q ∈ Q, degree F q = 15) ∧
      (outside F r).card = 14 ∧
      (∀ q ∈ Q, ∀ s ∈ Q, star (pencil F r q) s = star (pencil F r s) q) ∧
      (Q.biUnion (pencil F r)).card ≤ 14 := by
  have hd := all_degrees_ge15 F hcover hpub
  have hs : ∑ q : Point, degree F q = 203 := by
    rw [sum_degrees_uniform F 7 (fun B hB => (hcover.1 B hB).2), h29]
  have hf := five_minimum_degrees (degree F) hd hs
  let M := univ.filter (degree F · = 15)
  have hfM : 5 ≤ M.card := hf
  have hm : M.Nonempty := card_pos.mp (by omega)
  obtain ⟨r,hr⟩ := hm
  have hr15 : degree F r = 15 := (mem_filter.mp hr).2
  have he : 4 ≤ (M.erase r).card := by rw [card_erase_of_mem hr]; omega
  obtain ⟨Q,hQM,hQ⟩ := exists_subset_card_eq he
  have ho : (outside F r).card = 14 := by
    have := degree_add_outside F r
    omega
  refine ⟨r,Q,hQ,?_,hr15,?_,ho,?_,pencil_union_budget F r Q 14 (le_of_eq ho)⟩
  · intro hrQ
    exact (mem_erase.mp (hQM hrQ)).1 rfl
  · intro q hq
    exact (mem_filter.mp (mem_erase.mp (hQM hq)).2).2
  · intro q _ s _
    exact pencil_pair_agreement F r q s

end C13
