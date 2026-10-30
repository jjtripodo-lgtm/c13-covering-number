import C13Enumeration.PartialStar
import C13Covering.CheckerBridge
import C13Raw.Coding
namespace C13.Enumeration
open Finset
open C13.Checker.RawSupport

theorem list_map_finset {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (xs : List α) : (xs.map f).toFinset = xs.toFinset.image f := by
  ext y
  simp

/-- Decode the same thirteen physical bits directly in the typed point model. -/
def decodeTyped (b : Code) : Finset Point :=
  Finset.univ.filter fun p => b.getLsbD p.val = true

@[simp] theorem mem_decodeTyped (b : Code) (p : Point) :
    p ∈ decodeTyped b ↔ b.getLsbD p.val = true := by simp [decodeTyped]

theorem decodeTyped_or (a b : Code) : decodeTyped (a ||| b) = decodeTyped a ∪ decodeTyped b := by
  ext p
  simp [BitVec.getLsbD_or]

theorem decodeTyped_zero : decodeTyped (0 : Code) = ∅ := by
  ext p
  simp [decodeTyped]

theorem decodeTyped_single (p : Point) : decodeTyped (BitVec.twoPow 13 p.val) = {p} := by
  ext q
  simp [BitVec.getLsbD_twoPow,p.isLt,Fin.ext_iff,eq_comm]

/-- Structural recursion over all point labels; zero columns are not omitted
from either the domain of the map or its completeness proof. -/
def imageCodeAux (f : Point → Point) (b : Code) : List Point → Code
  | [] => 0
  | p :: ps => if b.getLsbD p.val then
      BitVec.twoPow 13 (f p).val ||| imageCodeAux f b ps
    else imageCodeAux f b ps

def imageCode (f : Point → Point) (b : Code) : Code :=
  imageCodeAux f b (List.finRange 13)

theorem decodeTyped_imageCodeAux (f : Point → Point) (b : Code) (ps : List Point) :
    decodeTyped (imageCodeAux f b ps) =
      ((ps.filter fun p => b.getLsbD p.val).toFinset).image f := by
  induction ps with
  | nil =>
    simpa only [imageCodeAux,List.filter_nil,List.toFinset_nil,Finset.image_empty] using decodeTyped_zero
  | cons p ps ih =>
    cases h : b.getLsbD p.val
    · simp only [imageCodeAux,h,Bool.false_eq_true,if_false,List.filter_cons,ih]
    · simp only [imageCodeAux,h,if_true,List.filter_cons,List.toFinset_cons,
        decodeTyped_or,decodeTyped_single,ih,Finset.image_insert,Finset.singleton_union]

theorem decodeTyped_imageCode (f : Point → Point) (b : Code) :
    decodeTyped (imageCode f b) = (decodeTyped b).image f := by
  rw [imageCode,decodeTyped_imageCodeAux]
  apply congrArg (Finset.image f)
  ext p
  simp [decodeTyped]

def decodeSource (bs : List Code) : Family Point := (bs.map decodeTyped).toFinset

def avoidCodes (bs : List Code) (c : Point) : List Code :=
  bs.filter fun b => !(b.getLsbD c.val)

def codedEmit (bs : List Code) (c q : Point) (f : Point → Point) : List Code :=
  ((avoidCodes bs c).map (imageCode f)).map fun b => BitVec.twoPow 13 q.val ||| b

theorem decodeSource_avoid (bs : List Code) (c : Point) :
    decodeSource (avoidCodes bs c) = outside (decodeSource bs) c := by
  ext B
  simp only [decodeSource,List.mem_toFinset,List.mem_map,avoidCodes,List.mem_filter,mem_outside]
  constructor
  · rintro ⟨b,⟨hb,hc⟩,rfl⟩
    exact ⟨⟨b,hb,rfl⟩,by simpa using hc⟩
  · rintro ⟨⟨b,hb,rfl⟩,hc⟩
    exact ⟨b,⟨hb,by simpa using hc⟩,rfl⟩

theorem decodeSource_image (bs : List Code) (f : Point → Point) :
    decodeSource (bs.map (imageCode f)) = mapFamily f (decodeSource bs) := by
  simp only [decodeSource,List.map_map,list_map_finset,mapFamily,Finset.image_image]
  apply image_congr
  intro b hb
  exact decodeTyped_imageCode f b

theorem decodeSource_lift (bs : List Code) (q : Point) :
    decodeSource (bs.map fun b => BitVec.twoPow 13 q.val ||| b) = liftAt q (decodeSource bs) := by
  simp only [decodeSource,List.map_map,list_map_finset,liftAt,Finset.image_image]
  apply image_congr
  intro b hb
  change decodeTyped (BitVec.twoPow 13 q.val ||| b) = insert q (decodeTyped b)
  rw [decodeTyped_or,decodeTyped_single]
  simp

theorem decodeSource_codedEmit (bs : List Code) (c q : Point) (f : Point → Point) :
    decodeSource (codedEmit bs c q f) = emitPencil (decodeSource bs) c q f := by
  rw [codedEmit,decodeSource_lift,decodeSource_image,decodeSource_avoid]
  rfl

theorem encodeBlock_decodeTyped (b : Code) : encodeBlock (decodeTyped b) = decode b := by
  ext n
  constructor
  · intro h
    obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp h
    simpa [decode,pointEmbedding,p.isLt] using hp
  · intro h
    have hn : n < 13 := (Finset.mem_filter.mp h).1 |> Finset.mem_range.mp
    refine Finset.mem_map.mpr ⟨⟨n,hn⟩,?_,rfl⟩
    exact (mem_decodeTyped b ⟨n,hn⟩).mpr (Finset.mem_filter.mp h).2

theorem encodeFamily_decodeSource (bs : List Code) :
    encodeFamily (decodeSource bs) = (decodePencil bs).toFinset := by
  simp only [encodeFamily,decodeSource,decodePencil,list_map_finset,Finset.image_image]
  apply image_congr
  intro b hb
  exact encodeBlock_decodeTyped b

/-- A small equality of bounded physical codes proves the exact representation
needed by the semantic checker bridge. No hash or numeric block ID is trusted. -/
theorem represents_of_code_eq (bs out : List Code) (K : Family Point)
    (hK : decodeSource bs = K) (c q : Point) (f : Point → Point)
    (hout : out.toFinset = (codedEmit bs c q f).toFinset) :
    RepresentsPencil (decodePencil out) (emitPencil K c q f) := by
  unfold RepresentsPencil
  rw [← encodeFamily_decodeSource]
  have hd : decodeSource out = decodeSource (codedEmit bs c q f) := by
    simp only [decodeSource,list_map_finset]
    rw [hout]
  rw [hd,decodeSource_codedEmit,hK]

/-- Preserve the chosen literal row and its labelled domain membership. -/
theorem decoded_row_mem (d : CodedDomain) (r : List (Fin d.alphabet.length))
    (hr : r ∈ d.rows) : decodePencil (d.pencil r) ∈ d.supported.domain.2 := by
  exact List.mem_map.mpr ⟨d.pencil r,List.mem_map.mpr ⟨r,hr,rfl⟩,rfl⟩
end C13.Enumeration
