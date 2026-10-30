import Mathlib.Data.Finset.Sort
import C13Covering.SourceBoundary
import C13.Checker

/-! The executable checker and the abstract covering argument use the same
literal block semantics. In particular, domains/pencils are compared as sets,
not by list order, multiplicity, block IDs, or hashes. -/
namespace C13
open Finset

def pointEmbedding : Point ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
def encodeBlock (B : Finset Point) : Finset ℕ := B.map pointEmbedding
def encodeFamily (P : Family Point) : Finset (Finset ℕ) := P.image encodeBlock

theorem encodeBlock_injective : Function.Injective encodeBlock := map_injective pointEmbedding

@[simp] theorem mem_encodeBlock (q : Point) (B : Finset Point) :
    q.val ∈ encodeBlock B ↔ q ∈ B := mem_map' pointEmbedding

@[simp] theorem encodeFamily_card (P : Family Point) : (encodeFamily P).card = P.card :=
  card_image_of_injective P encodeBlock_injective

/-- Extensional representation intentionally permits any pencil list order and
ignores duplicate list entries, matching literal set-valued pencils. -/
def RepresentsPencil (p : Checker.Pencil) (P : Family Point) : Prop :=
  p.toFinset = encodeFamily P

theorem shared_of_representation (p : Checker.Pencil) (P : Family Point)
    (h : RepresentsPencil p P) (q : Point) :
    Checker.shared p q.val = encodeFamily (star P q) := by
  ext b
  have hh : ∀ b, b ∈ p ↔ b ∈ encodeFamily P := by
    intro b
    rw [← h]
    exact List.mem_toFinset.symm
  simp only [Checker.shared,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,hh]
  constructor
  · rintro ⟨hb,hq⟩
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hb
    exact mem_image.mpr ⟨B,mem_star.mpr ⟨hB,(mem_encodeBlock q B).mp hq⟩,rfl⟩
  · intro hb
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hb
    obtain ⟨hBP,hqB⟩ := mem_star.mp hB
    exact ⟨mem_image.mpr ⟨B,hBP,rfl⟩,(mem_encodeBlock q B).mpr hqB⟩

theorem compatible_of_representation (p s : Checker.Pencil) (P S : Family Point)
    (hp : RepresentsPencil p P) (hs : RepresentsPencil s S) (q r : Point)
    (h : star P r = star S q) : Checker.Compatible q.val p r.val s := by
  unfold Checker.Compatible
  rw [shared_of_representation p P hp r,shared_of_representation s S hs q,h]

/-- Every encoded chosen block lies in the actual physical union. -/
theorem represented_union_subset (Q : Finset Point) (P : Point → Family Point)
    (chosen : Checker.Selected)
    (hchosen : ∀ x ∈ chosen, ∃ q ∈ Q, x.1 = q.val ∧ RepresentsPencil x.2 (P q)) :
    Checker.unionBlocks chosen ⊆ encodeFamily (Q.biUnion P) := by
  intro b hb
  obtain ⟨n,p,hp,hb⟩ := (Checker.mem_unionBlocks chosen b).mp hb
  obtain ⟨q,hq,_,hrep⟩ := hchosen (n,p) hp
  have hbp : b ∈ encodeFamily (P q) := by
    rw [← hrep]
    exact List.mem_toFinset.mpr hb
  obtain ⟨B,hB,rfl⟩ := mem_image.mp hbp
  exact mem_image.mpr ⟨B,mem_biUnion.mpr ⟨q,hq,hB⟩,rfl⟩

/-- Bridge from any order of the selected points and any extensional pencil
representatives to the recursive checker semantics. No residual reduction,
source enumeration, or arc pruning is implicit in this theorem. -/
theorem hasJoin_of_represented_selection (budget : ℕ) (Q : Finset Point)
    (P : Point → Family Point) (p : Point → Checker.Pencil)
    (D : Point → List Checker.Pencil)
    (hmem : ∀ q ∈ Q, p q ∈ D q)
    (hrep : ∀ q ∈ Q, RepresentsPencil (p q) (P q))
    (hpair : ∀ q ∈ Q, ∀ r ∈ Q, star (P q) r = star (P r) q)
    (hbudget : (Q.biUnion P).card ≤ budget)
    (qs : List Point) (hqs : ∀ q ∈ qs, q ∈ Q)
    (chosen : Checker.Selected)
    (hchosen : ∀ x ∈ chosen, ∃ q ∈ Q, x = (q.val,p q)) :
    Checker.HasJoin budget (qs.map fun q => (q.val,D q)) chosen := by
  induction qs generalizing chosen with
  | nil =>
    change (Checker.unionBlocks chosen).card ≤ budget
    have hsub := represented_union_subset Q P chosen (by
      intro x hx
      obtain ⟨q,hq,rfl⟩ := hchosen x hx
      exact ⟨q,hq,rfl,hrep q hq⟩)
    have hc := card_le_card hsub
    rw [encodeFamily_card] at hc
    exact hc.trans hbudget
  | cons q qs ih =>
    have hq := hqs q (List.mem_cons_self ..)
    change ∃ r ∈ D q, Checker.CompatibleWith chosen q.val r ∧
      Checker.HasJoin budget (qs.map fun s => (s.val,D s)) ((q.val,r)::chosen)
    refine ⟨p q,hmem q hq,?_,?_⟩
    · intro x hx
      obtain ⟨r,hr,rfl⟩ := hchosen x hx
      exact compatible_of_representation (p q) (p r) (P q) (P r)
        (hrep q hq) (hrep r hr) q r (hpair q hq r hr)
    · apply ih (fun r hr => hqs r (List.mem_cons_of_mem q hr))
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨q,hq,rfl⟩
      · exact hchosen x hx

/-- Needed direction only: executable domains may overapproximate all semantic
pencils, but may not silently omit any. No digest agreement can discharge this. -/
def ExecutableDomainsComplete (catalog : Finset (Family Point)) (hole : Point)
    (D : Family Point → Point → List Checker.Pencil) : Prop :=
  ∀ K ∈ catalog, ∀ q, q ≠ hole → ∀ P ∈ completeDomain catalog hole K hole q,
    ∃ p ∈ D K q, RepresentsPencil p P

/-- The complete finite obligation covers every catalog member and every fourset.
The sorted point order is an implementation convention, not a symmetry quotient. -/
def AllFourChecksFalse (catalog : Finset (Family Point)) (hole : Point)
    (D : Family Point → Point → List Checker.Pencil) : Prop :=
  ∀ K ∈ catalog, ∀ Q ∈ (univ.erase hole).powersetCard 4,
    Checker.hasJoinPrunedB 14 ((Q.sort (· ≤ ·)).map fun q => (q.val,D K q)) [] = false

theorem catalog_obstruction_of_complete_checked_domains
    (catalog : Finset (Family Point)) (hole : Point)
    (D : Family Point → Point → List Checker.Pencil)
    (hcomplete : ExecutableDomainsComplete catalog hole D)
    (hchecks : AllFourChecksFalse catalog hole D) : CatalogObstruction catalog hole := by
  classical
  intro K hK Q hQ P hP hpair hbudget
  have hQsub := (mem_powersetCard.mp hQ).1
  have hex : ∀ q : Point, ∃ p : Checker.Pencil,
      q ∈ Q → p ∈ D K q ∧ RepresentsPencil p (P q) := by
    intro q
    by_cases hq : q ∈ Q
    · obtain ⟨p,hp,hr⟩ := hcomplete K hK q (mem_erase.mp (hQsub hq)).1 (P q) (hP q hq)
      exact ⟨p,fun _ => ⟨hp,hr⟩⟩
    · exact ⟨[],fun h => False.elim (hq h)⟩
  choose p hp using hex
  have hj := hasJoin_of_represented_selection 14 Q P p (D K)
    (fun q hq => (hp q hq).1) (fun q hq => (hp q hq).2)
    hpair hbudget (Q.sort (· ≤ ·)) (by intro q hq; simpa using hq) [] (by simp)
  exact Checker.noJoin_of_pruned_check 14 _ (hchecks K hK Q hQ) hj

/-- This is a verified end-to-end reduction interface, not a completed lower
bound: source coverage, executable-domain completeness, and all-case Boolean
certificates remain explicit internal proof obligations. -/
theorem cover_card_ge30_from_complete_checked_domains
    (sources catalog : Finset (Family Point)) (hole : Point)
    (D : Family Point → Point → List Checker.Pencil)
    (hminimum : PublishedMinimumBound Point)
    (hpublished : ClassifiesMinimumLinks sources hole)
    (hcoverage : CatalogCoversSources sources catalog hole)
    (hcomplete : ExecutableDomainsComplete catalog hole D)
    (hchecks : AllFourChecksFalse catalog hole D)
    (F : Family Point) (hcover : IsCoverOn univ F 7 4) : 30 ≤ F.card :=
  cover_card_ge30_from_source_and_obstruction sources catalog hole hminimum hpublished hcoverage
    (catalog_obstruction_of_complete_checked_domains catalog hole D hcomplete hchecks) F hcover

end C13
