import C13Enumeration.PairProfile
import C13Enumeration.DegreeSeven.Lookup
import C13Enumeration.DomainWitness
namespace C13.Enumeration.Canonical
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

structure Template where
  family : Family Point
  center : Point
  center_ne : center ≠ hole
  avoids : ∀ B ∈ family, hole ∉ B
  matrix : Point → Point → Nat
  matrix_checked : ∀ a b, matrix a b = coDegree (link family center) a b

def Template.star (t : Template) := link t.family t.center

theorem Template.profile_invariant (t u : Template) (e : Equiv.Perm Point)
    (h : transport e t.star = u.star) : matrixProfile t.matrix = matrixProfile u.matrix := by
  rw [matrixProfile_eq_starProfile _ _ t.matrix_checked,
    matrixProfile_eq_starProfile _ _ u.matrix_checked]
  exact starProfile_transport _ _ e h

structure Record {n : Nat} (templates : Fin n → Template) where
  family : Family Point
  center : Point
  center_ne : center ≠ hole
  avoids : ∀ B ∈ family, hole ∉ B
  template : Fin n
  normalizer : Equiv.Perm Point
  hole_fixed : normalizer hole = hole
  center_image : normalizer center = (templates template).center
  star_image : transport normalizer (link family center) = (templates template).star

/-- The finite record list must cover every catalogue source and every one of
its twelve non-hole centers, regardless of star size or incidence fibers. -/
def Covers {n : Nat} {templates : Fin n → Template} (records : List (Record templates)) : Prop :=
  ∀ K ∈ catalog, ∀ c : Point, c ≠ hole →
    ∃ r ∈ records, r.family = K ∧ r.center = c

def UniqueTemplates {n : Nat} (templates : Fin n → Template) : Prop :=
  ∀ i j (e : Equiv.Perm Point), e hole = (templates j).center →
    e (templates i).center = hole → transport e (templates i).star = (templates j).star → i = j

def SourceComplete {n : Nat} {templates : Fin n → Template}
    (domains : Fin n → CodedDomain) (r : Record templates) : Prop :=
  r.family ∈ catalog → ∀ (e : Equiv.Perm Point),
    e hole = (templates r.template).center → e r.center = hole →
    transport e (link r.family r.center) = (templates r.template).star →
    ∃ p ∈ (domains r.template).supported.domain.2,
      RepresentsPencil p (emitPencil r.family r.center (templates r.template).center e)

theorem source_map_between {n : Nat} {templates : Fin n → Template}
    (r : Record templates) (j : Fin n) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e r.center = hole)
    (hs : transport e (link r.family r.center) = (templates j).star) :
    let g := r.normalizer.symm.trans e
    g hole = (templates j).center ∧ g (templates r.template).center = hole ∧
      transport g (templates r.template).star = (templates j).star := by
  dsimp
  have hhole : r.normalizer.symm hole = hole := by
    apply r.normalizer.injective
    simp [r.hole_fixed]
  have hcenter : r.normalizer.symm (templates r.template).center = r.center := by
    apply r.normalizer.injective
    simp [r.center_image]
  refine ⟨by simpa [hhole] using he,by simpa [hcenter] using hc,?_⟩
  rw [transport_trans]
  have hback : transport r.normalizer.symm (templates r.template).star =
      link r.family r.center := by rw [← r.star_image,transport_inverse]
  rw [hback]
  exact hs

theorem canonical_domains_complete {n : Nat} (templates : Fin n → Template)
    (domains : Fin n → CodedDomain) (records : List (Record templates))
    (hcover : Covers records) (hunique : UniqueTemplates templates)
    (hbound : ∀ r ∈ records, SourceComplete domains r) (j : Fin n) :
    ∀ P ∈ completeDomain catalog hole (templates j).family hole (templates j).center,
      ∃ p ∈ (domains j).supported.domain.2, RepresentsPencil p P := by
  intro P hP
  obtain ⟨K,hK,c,hc,e,he,hce,hs,hout⟩ :=
    C13.Raw.completeDomain_has_punctured_witness catalog hole (templates j).family
      hole (templates j).center (templates j).center_ne (templates j).avoids P hP
  obtain ⟨r,hr,rfl,rfl⟩ := hcover K hK c hc
  obtain ⟨hg1,hg2,hgs⟩ := source_map_between r j e he hce hs
  have hij := hunique r.template j (r.normalizer.symm.trans e) hg1 hg2 hgs
  subst j
  obtain ⟨p,hp,hrep⟩ := hbound r hr hK e he hce hs
  have hPout : emitPencil r.family r.center (templates r.template).center e = P := by
    unfold emitPencil
    rw [mapFamily_equiv]
    exact hout
  exact ⟨p,hp,hPout ▸ hrep⟩

def targetOfRecord {n : Nat} {templates : Fin n → Template}
    (domains : Fin n → CodedDomain)
    (hcomplete : ∀ j, ∀ P ∈ completeDomain catalog hole (templates j).family hole (templates j).center,
      ∃ p ∈ (domains j).supported.domain.2, RepresentsPencil p P)
    (r : Record templates) : DegreeSeven.Target where
  family := r.family
  point := r.center
  domain := relabelDomain (domains r.template) r.normalizer.symm r.center
  label := rfl
  complete := (complete_relabelled_domain catalog hole r.family (templates r.template).family
    r.center (templates r.template).center r.center_ne r.avoids (domains r.template)
    r.normalizer r.hole_fixed r.center_image r.star_image (hcomplete r.template)).2

theorem targets_cover {n : Nat} {templates : Fin n → Template}
    (domains : Fin n → CodedDomain)
    (hcomplete : ∀ j, ∀ P ∈ completeDomain catalog hole (templates j).family hole (templates j).center,
      ∃ p ∈ (domains j).supported.domain.2, RepresentsPencil p P)
    (records : List (Record templates)) (hcover : Covers records)
    (K : Family Point) (hK : K ∈ catalog) (q : Point) (hq : q ≠ hole) :
    ∃ t ∈ records.map (targetOfRecord domains hcomplete), t.family = K ∧ t.point = q := by
  obtain ⟨r,hr,hf,hc⟩ := hcover K hK q hq
  exact ⟨targetOfRecord domains hcomplete r,List.mem_map.mpr ⟨r,hr,rfl⟩,hf,hc⟩
end C13.Enumeration.Canonical
