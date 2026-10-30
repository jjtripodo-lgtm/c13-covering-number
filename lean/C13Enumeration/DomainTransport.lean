import C13Enumeration.RowTable
namespace C13.Enumeration
open Finset
open C13.Checker.RawSupport

@[simp] theorem encodeBlock_mem_family (B : Finset Point) (P : Family Point) :
    encodeBlock B ∈ encodeFamily P ↔ B ∈ P := by
  constructor
  · intro h
    obtain ⟨A,hA,hAB⟩ := Finset.mem_image.mp h
    exact encodeBlock_injective hAB ▸ hA
  · intro h
    exact Finset.mem_image.mpr ⟨B,h,rfl⟩

theorem encodeFamily_injective : Function.Injective encodeFamily := by
  intro P Q h
  ext B
  have hh := Finset.ext_iff.mp h (encodeBlock B)
  simpa only [encodeBlock_mem_family] using hh

theorem represents_decode_iff (bs : List Code) (P : Family Point) :
    RepresentsPencil (decodePencil bs) P ↔ decodeSource bs = P := by
  unfold RepresentsPencil
  rw [← encodeFamily_decodeSource]
  exact encodeFamily_injective.eq_iff

theorem represents_code_transport (bs out : List Code) (P : Family Point)
    (e : Equiv.Perm Point) (hrep : RepresentsPencil (decodePencil bs) P)
    (hcodes : out.toFinset = (bs.map (imageCode e)).toFinset) :
    RepresentsPencil (decodePencil out) (transport e P) := by
  apply (represents_decode_iff ..).mpr
  have hdecode := (represents_decode_iff ..).mp hrep
  have h : decodeSource out = decodeSource (bs.map (imageCode e)) := by
    simp only [decodeSource,list_map_finset]
    rw [hcodes,list_map_finset]
  rw [h,decodeSource_image,hdecode,mapFamily_equiv]

/-- Target-star normalization acts on every semantic pencil, without replacing
or shrinking the source catalog. -/
theorem completeDomain_target_transport (catalog : Finset (Family Point))
    (hole : Point) (L T : Family Point) (r q r' q' : Point)
    (hqr : q ≠ r) (havoid : ∀ B ∈ L, r ∉ B)
    (a : Equiv.Perm Point) (haq : a q = q') (har : a r = r')
    (hstar : transport a (link L q) = link T q')
    (P : Family Point) (hP : P ∈ completeDomain catalog hole L r q) :
    transport a P ∈ completeDomain catalog hole T r' q' := by
  obtain ⟨K,hK,c,hc,e,he,hce,hes,hout⟩ :=
    C13.Raw.completeDomain_has_punctured_witness catalog hole L r q hqr havoid P hP
  let g := e.trans a
  have hg1 : g hole = q' := by change a (e hole) = q'; rw [he,haq]
  have hg2 : g c = r' := by change a (e c) = r'; rw [hce,har]
  have hgs : transport g (link K c) = link T q' := by
    rw [transport_trans,hes,hstar]
  have hgp : liftAt q' (transport g (outside K c)) = transport a P := by
    calc
      _ = liftAt (a q) (transport a (transport e (outside K c))) := by rw [haq,transport_trans]
      _ = transport a (liftAt q (transport e (outside K c))) := (transport_liftAt a q _).symm
      _ = transport a P := congrArg (transport a) hout
  apply (mem_completeDomain_iff ..).mpr
  refine ⟨K,hK,g,hg1,C13.Raw.whole_star_of_punctured_star K T g c r' q' hg2 hgs,?_⟩
  rw [← C13.Raw.outside_pencil_from_center K g c r' q' hg2]
  exact hgp

/-- Literal raw-row transport, before pruning, carries its exact block codes. -/
def RowTransport (src dst : CodedDomain) (e : Equiv.Perm Point) : Prop :=
  ∀ r ∈ src.rows, ∃ s ∈ dst.rows,
    (dst.pencil s).toFinset = ((src.pencil r).map (imageCode e)).toFinset

theorem pencil_index_transport (src dst : CodedDomain) (e : Equiv.Perm Point)
    (indexMap : Fin src.alphabet.length → Fin dst.alphabet.length)
    (halphabet : ∀ i, imageCode e src.alphabet[i] = dst.alphabet[indexMap i])
    (r : List (Fin src.alphabet.length)) :
    (src.pencil r).map (imageCode e) = dst.pencil (r.map indexMap) := by
  simp only [CodedDomain.pencil,List.map_map]
  apply List.map_congr_left
  intro i hi
  exact halphabet i

/-- Checking index rows suffices once the physical alphabet permutation has
been proved. This avoids repeating large block decoding in every row check. -/
theorem row_transport_chunk (src dst : CodedDomain) (targetTable : RowTable dst)
    (e : Equiv.Perm Point)
    (indexMap : Fin src.alphabet.length → Fin dst.alphabet.length)
    (halphabet : ∀ i, imageCode e src.alphabet[i] = dst.alphabet[indexMap i])
    (rs : List (List (Fin src.alphabet.length)))
    (pick : Fin rs.length → targetTable.Index)
    (checked : ∀ i, (targetTable.row (pick i)).toFinset = ((rs.get i).map indexMap).toFinset) :
    ∀ r ∈ rs, ∃ s ∈ dst.rows,
      (dst.pencil s).toFinset = ((src.pencil r).map (imageCode e)).toFinset := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
  refine ⟨targetTable.row (pick i),targetTable.row_mem _,?_⟩
  rw [pencil_index_transport src dst e indexMap halphabet]
  simp only [CodedDomain.pencil,list_map_finset]
  rw [checked i,list_map_finset]

theorem row_transport_of_chunks (src dst : CodedDomain) (e : Equiv.Perm Point)
    (sourceTable : RowTable src)
    (h : ∀ rs ∈ sourceTable.chunks, ∀ r ∈ rs, ∃ s ∈ dst.rows,
      (dst.pencil s).toFinset = ((src.pencil r).map (imageCode e)).toFinset) :
    RowTransport src dst e := by
  intro r hr
  rw [← sourceTable.flatten_eq] at hr
  obtain ⟨rs,hrs,hr⟩ := List.mem_flatten.mp hr
  exact h rs hrs r hr

/-- Full target-domain completeness is preserved with literal row and point
label transport. No post-arc domain is substituted for a raw domain. -/
theorem complete_raw_domain_transport (catalog : Finset (Family Point))
    (hole : Point) (L : Family Point) (q b : Point) (hq : q ≠ hole)
    (havoid : ∀ B ∈ L, hole ∉ B) (src dst : CodedDomain)
    (hpoint : dst.supported.domain.1 = q.val)
    (a : Equiv.Perm Point) (ha : a hole = hole) (haq : a q = b)
    (hs : transport a (link L q) = link L b)
    (hbase : ∀ P ∈ completeDomain catalog hole L hole b,
      ∃ p ∈ src.supported.domain.2, RepresentsPencil p P)
    (hrows : RowTransport src dst a.symm) :
    dst.supported.domain.1 = q.val ∧ ∀ P ∈ completeDomain catalog hole L hole q,
      ∃ p ∈ dst.supported.domain.2, RepresentsPencil p P := by
  refine ⟨hpoint,?_⟩
  intro P hP
  have hb := completeDomain_target_transport catalog hole L L hole q hole b hq havoid a haq ha hs P hP
  obtain ⟨p,hp,hrep⟩ := hbase (transport a P) hb
  obtain ⟨cs,hcs,rfl⟩ := List.mem_map.mp hp
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hcs
  obtain ⟨s,hsrow,hcodes⟩ := hrows r hr
  refine ⟨decodePencil (dst.pencil s),decoded_row_mem dst s hsrow,?_⟩
  have h := represents_code_transport (src.pencil r) (dst.pencil s) (transport a P) a.symm hrep hcodes
  simpa only [transport_inverse] using h
end C13.Enumeration
