import C13Enumeration.CodeTransport
namespace C13.Enumeration
open C13.Checker.RawSupport

/-- A partition of the existing literal row list. Chunking changes neither the
rows nor their point labels; it only bounds certificate lookup costs. -/
structure RowTable (d : CodedDomain) where
  chunks : List (List (List (Fin d.alphabet.length)))
  flatten_eq : chunks.flatten = d.rows

def RowTable.Index {d : CodedDomain} (t : RowTable d) :=
  Σ i : Fin t.chunks.length, Fin (t.chunks.get i).length

def RowTable.row {d : CodedDomain} (t : RowTable d) (i : t.Index) :
    List (Fin d.alphabet.length) := (t.chunks.get i.1).get i.2

theorem RowTable.row_mem {d : CodedDomain} (t : RowTable d) (i : t.Index) :
    t.row i ∈ d.rows := by
  rw [← t.flatten_eq]
  exact List.mem_flatten.mpr
    ⟨t.chunks.get i.1,List.get_mem _ _,List.get_mem _ _⟩

def MapsRepresented (d : CodedDomain) (K : Family Point) (c q : Point)
    (a : Equiv.Perm Point) (maps : List (Point → Point)) : Prop :=
  ∀ f ∈ maps, ∃ p ∈ d.supported.domain.2,
    RepresentsPencil p (emitPencil K c q (fun x => f (a x)))

/-- Every proposed output is connected to a bounded index in an actual literal
raw row table. Producer-supplied hashes never enter the mathematical proof. -/
theorem mapsRepresented_of_code_checks (d : CodedDomain) (t : RowTable d)
    (bs : List Code) (K : Family Point) (hK : decodeSource bs = K)
    (c q : Point) (a : Equiv.Perm Point) (maps : List (Point → Point))
    (pick : Fin maps.length → t.Index)
    (checked : ∀ i : Fin maps.length,
      (d.pencil (t.row (pick i))).toFinset =
        (codedEmit bs c q (fun x => maps.get i (a x))).toFinset) :
    MapsRepresented d K c q a maps := by
  intro f hf
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hf
  refine ⟨decodePencil (d.pencil (t.row (pick i))),
    decoded_row_mem d _ (t.row_mem (pick i)),?_⟩
  exact represents_of_code_eq bs _ K hK c q _ (checked i)

/-- Normalization plus complete template-map enumeration covers each actual
unrestricted source-center pencil with a displayed raw row. -/
theorem source_center_represented (d : CodedDomain) (K T : Family Point)
    (hole c q : Point) (a : Equiv.Perm Point)
    (ha : a hole = hole) (hac : a c = q)
    (hs : transport a (link K c) = link T q)
    (maps : List (Point → Point))
    (hcomplete : ∀ g : Equiv.Perm Point, g hole = q → g q = hole →
      transport g (link T q) = link T q → (g : Point → Point) ∈ maps)
    (hreps : MapsRepresented d K c q a maps)
    (e : Equiv.Perm Point) (he : e hole = q) (hec : e c = hole)
    (hes : transport e (link K c) = link T q) :
    ∃ p ∈ d.supported.domain.2, RepresentsPencil p (emitPencil K c q e) := by
  obtain ⟨hg1,hg2,hgs,hf⟩ := source_map_factors K T hole c q a e ha hac hs he hec hes
  obtain ⟨p,hp,hrep⟩ := hreps (a.symm.trans e) (hcomplete _ hg1 hg2 hgs)
  refine ⟨p,hp,?_⟩
  have hfun : (fun x => (a.symm.trans e) (a x)) = (e : Point → Point) := funext hf
  rw [hfun] at hrep
  exact hrep
end C13.Enumeration
