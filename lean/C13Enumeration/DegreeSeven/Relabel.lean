import C13Enumeration.DomainTransport
namespace C13.Enumeration
open C13.Checker.RawSupport
set_option Elab.async false

/-- A computable ambient relabelling retains every indexed row and changes the
physical block alphabet and point label together. -/
def relabelDomain (d : CodedDomain) (e : Equiv.Perm Point) (q : Point) : CodedDomain where
  point := q.val
  alphabet := d.alphabet.map (imageCode e)
  rows := d.rows.map (List.map (fun i => ⟨i.val,by simpa using i.isLt⟩))

def relabelIndex (d : CodedDomain) (e : Equiv.Perm Point) (q : Point)
    (i : Fin d.alphabet.length) : Fin (relabelDomain d e q).alphabet.length :=
  ⟨i.val,by simpa [relabelDomain] using i.isLt⟩

theorem relabel_alphabet (d : CodedDomain) (e : Equiv.Perm Point) (q : Point)
    (i : Fin d.alphabet.length) :
    imageCode e d.alphabet[i] = (relabelDomain d e q).alphabet[relabelIndex d e q i] := by
  simp [relabelDomain,relabelIndex]

theorem relabel_rows (d : CodedDomain) (e : Equiv.Perm Point) (q : Point) :
    RowTransport d (relabelDomain d e q) e := by
  intro r hr
  refine ⟨r.map (relabelIndex d e q),?_,?_⟩
  · exact List.mem_map.mpr ⟨r,hr,rfl⟩
  · exact congrArg List.toFinset (pencil_index_transport d (relabelDomain d e q) e
      (relabelIndex d e q) (relabel_alphabet d e q) r).symm

/-- Star normalization transports complete coded domains between distinct root
families; the source catalogue remains fixed throughout. -/
theorem complete_relabelled_domain (catalog : Finset (Family Point))
    (hole : Point) (L T : Family Point) (q b : Point) (hq : q ≠ hole)
    (havoid : ∀ B ∈ L, hole ∉ B) (src : CodedDomain)
    (a : Equiv.Perm Point) (ha : a hole = hole) (haq : a q = b)
    (hs : transport a (link L q) = link T b)
    (hbase : ∀ P ∈ completeDomain catalog hole T hole b,
      ∃ p ∈ src.supported.domain.2, RepresentsPencil p P) :
    (relabelDomain src a.symm q).supported.domain.1 = q.val ∧
    ∀ P ∈ completeDomain catalog hole L hole q,
      ∃ p ∈ (relabelDomain src a.symm q).supported.domain.2, RepresentsPencil p P := by
  refine ⟨rfl,?_⟩
  intro P hP
  have hb := completeDomain_target_transport catalog hole L T hole q hole b hq havoid a haq ha hs P hP
  obtain ⟨p,hp,hrep⟩ := hbase (transport a P) hb
  obtain ⟨cs,hcs,rfl⟩ := List.mem_map.mp hp
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hcs
  obtain ⟨s,hsrow,hcodes⟩ := relabel_rows src a.symm q r hr
  refine ⟨decodePencil ((relabelDomain src a.symm q).pencil s),
    decoded_row_mem _ s hsrow,?_⟩
  have h := represents_code_transport (src.pencil r)
    ((relabelDomain src a.symm q).pencil s) (transport a P) a.symm hrep hcodes
  simpa only [transport_inverse] using h
end C13.Enumeration
