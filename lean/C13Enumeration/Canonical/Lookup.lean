import C13Enumeration.Canonical.Core
namespace C13.Enumeration.Canonical
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Select the normalizer before relabelling rows. This avoids eagerly
constructing hundreds of copies of the large raw domains. -/
def lookupRecord {n : Nat} {templates : Fin n → Template}
    (records : List (Record templates)) (K : Family Point) (q : Point) : Option (Record templates) :=
  match records with
  | [] => none
  | r :: rs => if r.center = q ∧ r.family = K then some r else lookupRecord rs K q

theorem lookupRecord_exists {n : Nat} {templates : Fin n → Template}
    (records : List (Record templates)) (K : Family Point) (q : Point)
    (h : ∃ r ∈ records, r.family = K ∧ r.center = q) :
    ∃ r, lookupRecord records K q = some r ∧ r.family = K ∧ r.center = q := by
  induction records with
  | nil => simp at h
  | cons r rs ih =>
    by_cases hm : r.center = q ∧ r.family = K
    · exact ⟨r,by simp [lookupRecord,hm],hm.2,hm.1⟩
    · have htail : ∃ t ∈ rs, t.family = K ∧ t.center = q := by
        obtain ⟨t,ht,hf,hq⟩ := h
        rcases List.mem_cons.mp ht with rfl | ht
        · exact (hm ⟨hq,hf⟩).elim
        · exact ⟨t,ht,hf,hq⟩
      obtain ⟨t,ht,hf,hq⟩ := ih htail
      exact ⟨t,by simpa [lookupRecord,hm] using ht,hf,hq⟩

def lookupDomain {n : Nat} {templates : Fin n → Template}
    (domains : Fin n → CodedDomain) (records : List (Record templates))
    (K : Family Point) (q : Point) : CodedDomain :=
  match lookupRecord records K q with
  | none => {point := q.val,alphabet := [],rows := []}
  | some r => relabelDomain (domains r.template) r.normalizer.symm q

theorem lookupDomain_label {n : Nat} {templates : Fin n → Template}
    (domains : Fin n → CodedDomain) (records : List (Record templates))
    (K : Family Point) (q : Point) : (lookupDomain domains records K q).supported.domain.1 = q.val := by
  unfold lookupDomain
  split <;> rfl

theorem lookupDomain_complete {n : Nat} {templates : Fin n → Template}
    (domains : Fin n → CodedDomain)
    (hcomplete : ∀ j, ∀ P ∈ completeDomain catalog hole (templates j).family hole (templates j).center,
      ∃ p ∈ (domains j).supported.domain.2, RepresentsPencil p P)
    (records : List (Record templates)) (hcover : Covers records)
    (K : Family Point) (hK : K ∈ catalog) (q : Point) (hq : q ≠ hole) :
    ∀ P ∈ completeDomain catalog hole K hole q,
      ∃ p ∈ (lookupDomain domains records K q).supported.domain.2, RepresentsPencil p P := by
  obtain ⟨r,hr,rfl,rfl⟩ := lookupRecord_exists records K q (hcover K hK q hq)
  unfold lookupDomain
  rw [hr]
  exact (complete_relabelled_domain catalog hole r.family (templates r.template).family
    r.center (templates r.template).center r.center_ne r.avoids (domains r.template)
    r.normalizer r.hole_fixed r.center_image r.star_image (hcomplete r.template)).2
end C13.Enumeration.Canonical
