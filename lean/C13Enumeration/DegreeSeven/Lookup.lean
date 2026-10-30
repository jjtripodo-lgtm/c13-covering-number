import C13Enumeration.DegreeSeven.Relabel
import C13Covering.SourceLiterals
namespace C13.Enumeration.DegreeSeven
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false

/-- A complete labelled coded domain at one literal catalogue target. The proof
field does not alter its executable alphabet or row data. -/
structure Target where
  family : Family Point
  point : Point
  domain : CodedDomain
  label : domain.supported.domain.1 = point.val
  complete : ∀ P ∈ completeDomain catalog hole family hole point,
    ∃ p ∈ domain.supported.domain.2, RepresentsPencil p P

def normalizedTarget (K : Family Point) (q b : Point) (src : CodedDomain)
    (a : Equiv.Perm Point) (hq : q ≠ hole) (havoid : ∀ B ∈ K, hole ∉ B)
    (ha : a hole = hole) (haq : a q = b)
    (hs : transport a (link K q) = link link09 b)
    (hbase : ∀ P ∈ completeDomain catalog hole link09 hole b,
      ∃ p ∈ src.supported.domain.2, RepresentsPencil p P) : Target where
  family := K
  point := q
  domain := relabelDomain src a.symm q
  label := rfl
  complete := (complete_relabelled_domain catalog hole K link09 q b hq havoid src a
    ha haq hs hbase).2

/-- Empty outside the explicitly certified target list; completeness is claimed
only under proved list coverage, never by interpreting this fallback as data. -/
def lookup (targets : List Target) (K : Family Point) (q : Point) : CodedDomain :=
  match targets with
  | [] => {point := q.val, alphabet := [], rows := []}
  | t :: ts => if t.family = K ∧ t.point = q then t.domain else lookup ts K q

theorem lookup_label (targets : List Target) (K : Family Point) (q : Point) :
    (lookup targets K q).supported.domain.1 = q.val := by
  induction targets with
  | nil => rfl
  | cons t ts ih =>
    by_cases h : t.family = K ∧ t.point = q
    · simp only [lookup,if_pos h]
      simpa only [h.2] using t.label
    · simpa only [lookup,if_neg h] using ih

theorem lookup_complete (targets : List Target) (K : Family Point) (q : Point)
    (h : ∃ t ∈ targets, t.family = K ∧ t.point = q) :
    ∀ P ∈ completeDomain catalog hole K hole q,
      ∃ p ∈ (lookup targets K q).supported.domain.2, RepresentsPencil p P := by
  induction targets with
  | nil => simp at h
  | cons t ts ih =>
    by_cases ht : t.family = K ∧ t.point = q
    · simp only [lookup,if_pos ht]
      rcases ht with ⟨rfl,rfl⟩
      exact t.complete
    · simp only [lookup,if_neg ht]
      apply ih
      obtain ⟨u,hu,huf,huq⟩ := h
      rcases List.mem_cons.mp hu with rfl | hu
      · exact (ht ⟨huf,huq⟩).elim
      · exact ⟨u,hu,huf,huq⟩

theorem target_mem_flatten (groups : List (List Target)) (part : List Target)
    (hpart : part ∈ groups) (K : Family Point) (q : Point)
    (h : ∃ t ∈ part, t.family = K ∧ t.point = q) :
    ∃ t ∈ groups.flatten, t.family = K ∧ t.point = q := by
  obtain ⟨t,ht,hf,hq⟩ := h
  exact ⟨t,List.mem_flatten.mpr ⟨part,hpart,ht⟩,hf,hq⟩
end C13.Enumeration.DegreeSeven
