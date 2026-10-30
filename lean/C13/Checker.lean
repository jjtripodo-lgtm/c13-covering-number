import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Perm.Subperm

/-! A kernel-checkable finite search seam. Inputs are literal physical block sets.
No claim of source catalog or reconstructed-domain completeness is made here. -/
namespace C13.Checker

abbrev Block := Finset Nat
abbrev Pencil := List Block
abbrev Domain := Nat × List Pencil
abbrev Selected := List (Nat × Pencil)

def shared (p : Pencil) (q : Nat) : Finset Block :=
  (p.filter fun b => decide (q ∈ b)).toFinset

def Compatible (q : Nat) (p : Pencil) (r : Nat) (s : Pencil) : Prop :=
  shared p r = shared s q

instance (q : Nat) (p : Pencil) (r : Nat) (s : Pencil) :
    Decidable (Compatible q p r s) := inferInstanceAs (Decidable (_ = _))

def CompatibleWith (chosen : Selected) (q : Nat) (p : Pencil) : Prop :=
  ∀ x ∈ chosen, Compatible q p x.1 x.2

instance (chosen : Selected) (q : Nat) (p : Pencil) :
    Decidable (CompatibleWith chosen q p) :=
  inferInstanceAs (Decidable (∀ x ∈ chosen, Compatible q p x.1 x.2))

def unionBlocks (chosen : Selected) : Finset Block :=
  (chosen.flatMap Prod.snd).toFinset

def WithinBudget (budget : Nat) (chosen : Selected) : Prop :=
  (unionBlocks chosen).card ≤ budget

instance (budget : Nat) (chosen : Selected) : Decidable (WithinBudget budget chosen) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Exact unpruned finite semantics, indexed by the supplied domain list. -/
def HasJoin (budget : Nat) : List Domain → Selected → Prop
  | [], chosen => WithinBudget budget chosen
  | (q, ps) :: ds, chosen =>
    ∃ p ∈ ps, CompatibleWith chosen q p ∧ HasJoin budget ds ((q,p) :: chosen)

/-- Exact finite checker. Compatibility is tested on literal blocks, never a hash. -/
def hasJoinB (budget : Nat) : List Domain → Selected → Bool
  | [], chosen => decide (WithinBudget budget chosen)
  | (q, ps) :: ds, chosen => ps.any fun p =>
    decide (CompatibleWith chosen q p) && hasJoinB budget ds ((q,p) :: chosen)

theorem hasJoinB_iff (budget : Nat) (domains : List Domain) (chosen : Selected) :
    hasJoinB budget domains chosen = true ↔ HasJoin budget domains chosen := by
  induction domains generalizing chosen with
  | nil => simp [hasJoinB, HasJoin]
  | cons d ds ih =>
    rcases d with ⟨q, ps⟩
    simp only [hasJoinB, HasJoin, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact exists_congr fun p => and_congr_right fun _ => and_congr_right fun _ => ih _

theorem noJoin_of_check (budget : Nat) (domains : List Domain)
    (h : hasJoinB budget domains [] = false) : ¬ HasJoin budget domains [] := by
  intro hj
  have ht := (hasJoinB_iff budget domains []).mpr hj
  simp [h] at ht

/-- The block projection used by the checker is the actual union of physical pencils. -/
theorem mem_unionBlocks (chosen : Selected) (b : Block) :
    b ∈ unionBlocks chosen ↔ ∃ q p, (q,p) ∈ chosen ∧ b ∈ p := by
  simp only [unionBlocks, List.mem_toFinset, List.mem_flatMap]
  constructor
  · rintro ⟨⟨q,p⟩, h, hb⟩
    exact ⟨q,p,h,hb⟩
  · rintro ⟨q,p,h,hb⟩
    exact ⟨(q,p),h,hb⟩

/-- Literal shared-incidence equality is equivalent to equality for every physical block. -/
theorem compatible_iff (q : Nat) (p : Pencil) (r : Nat) (s : Pencil) :
    Compatible q p r s ↔ ∀ b, (b ∈ p ∧ r ∈ b) ↔ (b ∈ s ∧ q ∈ b) := by
  simp only [Compatible, Finset.ext_iff, shared, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq]

def coversB (cover : List Block) (queries : List Block) : Bool :=
  queries.all fun t => cover.any fun b => decide (t ⊆ b)

theorem coversB_iff (cover queries : List Block) :
    coversB cover queries = true ↔ ∀ t ∈ queries, ∃ b ∈ cover, t ⊆ b := by
  simp [coversB, List.all_eq_true, List.any_eq_true]

/-- A finite coverage certificate upgrades to all cardinality-t subsets once its
query list is shown complete. The completeness premise cannot be omitted. -/
theorem covers_all_of_complete (cover queries : List Block) (ground : Block) (t : Nat)
    (complete : ∀ q, q ⊆ ground → q.card = t → q ∈ queries)
    (checked : coversB cover queries = true) :
    ∀ q, q ⊆ ground → q.card = t → ∃ b ∈ cover, q ⊆ b := by
  intro q hq hc
  exact (coversB_iff cover queries).mp checked q (complete q hq hc)

/-- Complete query enumeration from an explicit finite ground list. -/
def queriesOf (ground : List Nat) (t : Nat) : List Block :=
  (ground.sublistsLen t).map List.toFinset

theorem queriesOf_complete (ground : List Nat) (t : Nat) (q : Block)
    (hq : q ⊆ ground.toFinset) (hc : q.card = t) : q ∈ queriesOf ground t := by
  have hs : q.toList ⊆ ground := by
    intro x hx
    exact List.mem_toFinset.mp (hq (Finset.mem_toList.mp hx))
  obtain ⟨l, hp, hl⟩ := List.subperm_of_subset q.nodup_toList hs
  apply List.mem_map.mpr
  refine ⟨l, List.mem_sublistsLen.mpr ⟨hl, ?_⟩, ?_⟩
  · exact hp.length_eq.trans ((Finset.length_toList q).trans hc)
  · apply Finset.ext
    intro x
    simp only [List.mem_toFinset]
    exact hp.mem_iff.trans Finset.mem_toList

theorem unionBlocks_subset_cons (chosen : Selected) (q : Nat) (p : Pencil) :
    unionBlocks chosen ⊆ unionBlocks ((q,p) :: chosen) := by
  intro b hb
  simp only [unionBlocks, List.flatMap_cons, List.mem_toFinset, List.mem_append] at *
  exact Or.inr hb

theorem budget_of_cons {budget q : Nat} {chosen : Selected} {p : Pencil}
    (h : WithinBudget budget ((q,p) :: chosen)) : WithinBudget budget chosen := by
  exact le_trans (Finset.card_le_card (unionBlocks_subset_cons chosen q p)) h

theorem HasJoin.withinBudget {budget : Nat} {domains : List Domain} {chosen : Selected}
    (h : HasJoin budget domains chosen) : WithinBudget budget chosen := by
  induction domains generalizing chosen with
  | nil => exact h
  | cons d ds ih =>
    rcases d with ⟨q,ps⟩
    obtain ⟨p, _, _, hj⟩ := h
    exact budget_of_cons (ih hj)

/-- Same exact decision with an early physical union-budget rejection. -/
def hasJoinPrunedB (budget : Nat) : List Domain → Selected → Bool
  | [], chosen => decide (WithinBudget budget chosen)
  | (q, ps) :: ds, chosen => ps.any fun p =>
    decide (CompatibleWith chosen q p) &&
    decide (WithinBudget budget ((q,p) :: chosen)) &&
    hasJoinPrunedB budget ds ((q,p) :: chosen)

theorem hasJoinPrunedB_iff (budget : Nat) (domains : List Domain) (chosen : Selected) :
    hasJoinPrunedB budget domains chosen = true ↔ HasJoin budget domains chosen := by
  induction domains generalizing chosen with
  | nil => simp [hasJoinPrunedB, HasJoin]
  | cons d ds ih =>
    rcases d with ⟨q,ps⟩
    simp only [hasJoinPrunedB, HasJoin, List.any_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    constructor
    · rintro ⟨p, hp, ⟨hcomp, _⟩, hj⟩
      exact ⟨p, hp, hcomp, (ih _).mp hj⟩
    · rintro ⟨p, hp, hcomp, hj⟩
      exact ⟨p, hp, ⟨hcomp, hj.withinBudget⟩, (ih _).mpr hj⟩

theorem noJoin_of_pruned_check (budget : Nat) (domains : List Domain)
    (h : hasJoinPrunedB budget domains [] = false) : ¬ HasJoin budget domains [] := by
  intro hj
  have ht := (hasJoinPrunedB_iff budget domains []).mpr hj
  simp [h] at ht

/-- Proof-carrying coverage: the certificate supplies a block index for each
query. Indices and literal containment are checked; no search is trusted. -/
def coverageWitnessB (cover : List Block) : List Block → List Nat → Bool
  | [], [] => true
  | q :: qs, i :: is =>
    match cover[i]? with
    | none => false
    | some b => decide (q ⊆ b) && coverageWitnessB cover qs is
  | _, _ => false

theorem coverageWitness_sound (cover queries : List Block) (witness : List Nat)
    (h : coverageWitnessB cover queries witness = true) :
    ∀ q ∈ queries, ∃ b ∈ cover, q ⊆ b := by
  induction queries generalizing witness with
  | nil => simp
  | cons q qs ih =>
    cases witness with
    | nil => simp [coverageWitnessB] at h
    | cons i is =>
      cases he : cover[i]? with
      | none => simp [coverageWitnessB, he] at h
      | some b =>
        have hh : q ⊆ b ∧ coverageWitnessB cover qs is = true := by
          simpa [coverageWitnessB, he] using h
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨b, List.mem_of_getElem? he, hh.1⟩
        · exact ih is hh.2 t ht

/-- An explicit four-domain expansion of the exact physical meaning. -/
theorem four_join_iff (budget a b c d : Nat) (A B C D : List Pencil) :
    HasJoin budget [(a,A),(b,B),(c,C),(d,D)] [] ↔
    ∃ p ∈ A, ∃ q ∈ B, ∃ r ∈ C, ∃ s ∈ D,
      Compatible b q a p ∧
      Compatible c r b q ∧ Compatible c r a p ∧
      Compatible d s c r ∧ Compatible d s b q ∧ Compatible d s a p ∧
      (unionBlocks [(d,s),(c,r),(b,q),(a,p)]).card ≤ budget := by
  simp [HasJoin, CompatibleWith, WithinBudget]
  constructor
  · rintro ⟨p,hp,q,hq,hqp,r,hr,⟨hrq,hrp⟩,s,hs,⟨hsr,hsq,hsp⟩,hb⟩
    exact ⟨p,hp,q,hq,r,hr,s,hs,hqp,hrq,hrp,hsr,hsq,hsp,hb⟩
  · rintro ⟨p,hp,q,hq,r,hr,s,hs,hqp,hrq,hrp,hsr,hsq,hsp,hb⟩
    exact ⟨p,hp,q,hq,hqp,r,hr,⟨hrq,hrp⟩,s,hs,⟨hsr,hsq,hsp⟩,hb⟩

end C13.Checker
