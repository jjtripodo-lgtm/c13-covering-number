import C13Covering.ClassifiedPencils

namespace C13
open Finset
variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
@[simp] theorem map_inverse (e : Equiv.Perm V) (B : Finset V) :
    (B.map e.toEmbedding).map e.symm.toEmbedding = B := by
  ext x
  simp

@[simp] theorem transport_inverse (e : Equiv.Perm V) (F : Family V) :
    transport e.symm (transport e F) = F := by
  simp only [transport,image_image]
  calc
    _ = F.image id := image_congr (by intro B _; exact map_inverse e B)
    _ = F := image_id

@[simp] theorem transport_card (e : Equiv.Perm V) (F : Family V) :
    (transport e F).card = F.card :=
  card_image_of_injective F (map_injective e.toEmbedding)

theorem transport_star (e : Equiv.Perm V) (F : Family V) (q : V) :
    transport e (star F q) = star (transport e F) (e q) := by
  ext B
  constructor
  · intro hB
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hB
    obtain ⟨hAF,hqA⟩ := mem_star.mp hA
    exact mem_star.mpr ⟨mem_image.mpr ⟨A,hAF,rfl⟩,by simpa using hqA⟩
  · intro hB
    obtain ⟨hBF,hqB⟩ := mem_star.mp hB
    obtain ⟨A,hAF,rfl⟩ := mem_image.mp hBF
    exact mem_image.mpr ⟨A,mem_star.mpr ⟨hAF,by simpa using hqB⟩,rfl⟩

theorem transport_link (e : Equiv.Perm V) (F : Family V) (q : V) :
    transport e (link F q) = link (transport e F) (e q) := by
  unfold link
  rw [← transport_star]
  simp only [transport,image_image]
  apply image_congr
  intro B _
  exact map_erase e.toEmbedding B q

theorem transport_cover [Fintype V] (e : Equiv.Perm V) {F : Family V} {k t : ℕ}
    (h : IsCoverOn univ F k t) : IsCoverOn univ (transport e F) k t := by
  constructor
  · intro B hB
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hB
    exact ⟨subset_univ _,by simpa using (h.1 A hA).2⟩
  · intro T _ hT
    have ht : (T.map e.symm.toEmbedding).card = t := by simpa using hT
    obtain ⟨B,hB,hTB⟩ := h.2 (T.map e.symm.toEmbedding) (subset_univ _) ht
    refine ⟨B.map e.toEmbedding,mem_image.mpr ⟨B,hB,rfl⟩,?_⟩
    have hh := (map_subset_map (f := e.toEmbedding)).mpr hTB
    have hback : (T.map e.symm.toEmbedding).map e.toEmbedding = T := by
      ext x
      simp
    rw [hback] at hh
    exact hh

/-- A normalized 29-cover has a literal catalog root. No catalog representative
is dropped, and no orbit assumption on the selected four points is used. -/
theorem normalize_cover29 (catalog : Finset (Family Point)) (hole : Point)
    (hpub : PublishedMinimumBound Point) (hclass : ClassifiesMinimumLinks catalog hole)
    (F : Family Point) (hcover : IsCoverOn univ F 7 4) (h29 : F.card = 29) :
    ∃ (K : Family Point) (G : Family Point), K ∈ catalog ∧
      IsCoverOn univ G 7 4 ∧ G.card = 29 ∧ link G hole = K ∧ degree G hole = 15 := by
  obtain ⟨r,Q,hQ,hrQ,hr,hrest⟩ := cover29_reduction F hcover h29 hpub
  obtain ⟨K,hK,e,he,hL⟩ := hclass r (link F r)
    (link_isCoverOn hcover (mem_univ r)) (by rw [link_card,hr])
  let G := transport e.symm F
  have hl : link G hole = K := by
    have hh := transport_link e.symm F r
    have hhq : e.symm r = hole := by rw [← he]; simp
    rw [hhq] at hh
    change link (transport e.symm F) hole = K
    rw [← hh,← hL,transport_inverse]
  refine ⟨K,G,hK,transport_cover e.symm hcover,by simpa [G] using h29,hl,?_⟩
  have hk : K.card = 15 := by
    rw [← transport_card e K,hL,link_card,hr]
  rw [← link_card,hl,hk]

/-- Obstruction for every literal catalog root and every four-element subset of
the other twelve points. This is a precise finite-certificate obligation, NOT a
proved census or a substitute for the source classification. -/
def CatalogObstruction (catalog : Finset (Family Point)) (hole : Point) : Prop :=
  ∀ K ∈ catalog, ∀ Q ∈ (univ.erase hole).powersetCard 4,
    ∀ P : Point → Family Point,
      (∀ q ∈ Q, P q ∈ completeDomain catalog hole K hole q) →
      (∀ q ∈ Q, ∀ s ∈ Q, star (P q) s = star (P s) q) →
      ¬ (Q.biUnion P).card ≤ 14

/-- If the all-class finite obstruction is proved, the two explicitly named
published prerequisites suffice to exclude an actual 29-block cover. -/
theorem no_cover29_of_catalog_obstruction (catalog : Finset (Family Point)) (hole : Point)
    (hpub : PublishedMinimumBound Point) (hclass : ClassifiesMinimumLinks catalog hole)
    (hfinite : CatalogObstruction catalog hole)
    (F : Family Point) (hcover : IsCoverOn univ F 7 4) : F.card ≠ 29 := by
  intro h29
  obtain ⟨K,G,hK,hG,hG29,hroot,hdroot⟩ := normalize_cover29 catalog hole hpub hclass F hcover h29
  have hd := all_degrees_ge15 G hG hpub
  have hs : ∑ q : Point, degree G q = 203 := by
    rw [sum_degrees_uniform G 7 (fun B hB => (hG.1 B hB).2),hG29]
  have hf := five_minimum_degrees (degree G) hd hs
  let M := univ.filter (degree G · = 15)
  have hm : hole ∈ M := mem_filter.mpr ⟨mem_univ _,hdroot⟩
  have hfm : 5 ≤ M.card := hf
  have he : 4 ≤ (M.erase hole).card := by rw [card_erase_of_mem hm]; omega
  obtain ⟨Q,hQM,hQ⟩ := exists_subset_card_eq he
  have hQuniv : Q ⊆ univ.erase hole := by
    intro q hq
    exact mem_erase.mpr ⟨(mem_erase.mp (hQM hq)).1,mem_univ _⟩
  have hmem : ∀ q ∈ Q, pencil G hole q ∈ completeDomain catalog hole K hole q := by
    intro q hq
    rw [← hroot]
    exact actual_pencil_mem_completeDomain catalog hole hclass G hG
      (mem_erase.mp (hQM hq)).1
      (mem_filter.mp (mem_erase.mp (hQM hq)).2).2
  have ho : (outside G hole).card = 14 := by
    have := degree_add_outside G hole
    omega
  exact hfinite K hK Q (mem_powersetCard.mpr ⟨hQuniv,hQ⟩) (pencil G hole) hmem
    (fun q _ s _ => pencil_pair_agreement G hole q s)
    (pencil_union_budget G hole Q 14 (le_of_eq ho))

/-- Number of selected-point configurations per source class, independent of
any source symmetry and including every four-subset. -/
theorem four_point_configuration_count (hole : Point) :
    ((univ.erase hole).powersetCard 4).card = 495 := by
  rw [card_powersetCard]
  simp only [card_erase_of_mem (mem_univ hole),card_univ,Fintype.card_fin]
  decide

/-- Bookkeeping counts only; these do not certify catalog/domain completeness. -/
theorem full_scope_counts (hole : Point) :
    68 * (univ.erase hole).card = 816 ∧
    68 * ((univ.erase hole).powersetCard 4).card = 33660 := by
  rw [four_point_configuration_count]
  simp

end C13
