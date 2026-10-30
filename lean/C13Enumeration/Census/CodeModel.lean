import C13Enumeration.Census.RowBits
import C13Enumeration.DomainTransport

namespace C13.Enumeration.Census
open Finset C13.Checker.RawSupport
set_option Elab.async false

theorem decodeTyped_injective : Function.Injective decodeTyped := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh : a.getLsbD i = true ↔ b.getLsbD i = true := by
    simpa using (Finset.ext_iff.mp h (⟨i,hi⟩ : Point))
  cases ha : a.getLsbD i <;> cases hb : b.getLsbD i <;> simp_all

def encodeTyped (B : Finset Point) : Code := rowBits ((List.finRange 13).filter fun p => p ∈ B)

@[simp] theorem decode_encodeTyped (B : Finset Point) :
    decodeTyped (encodeTyped B) = B := by
  ext p
  simp only [mem_decodeTyped,encodeTyped,rowBits_bit]
  simp

theorem encodeTyped_injective : Function.Injective encodeTyped := by
  intro A B h
  have hh := congrArg decodeTyped h
  simpa using hh

@[simp] theorem encode_decodeTyped (c : Code) : encodeTyped (decodeTyped c) = c := by
  apply decodeTyped_injective
  simp

def subsetB (a b : Code) : Bool := (a &&& b) == a

theorem subsetB_iff (a b : Code) : subsetB a b = true ↔ decodeTyped a ⊆ decodeTyped b := by
  unfold subsetB
  rw [beq_iff_eq]
  constructor
  · intro h p hp
    have ha := (mem_decodeTyped a p).1 hp
    have he := congrArg (fun c : Code => c.getLsbD p.val) h
    apply (mem_decodeTyped b p).2
    simpa [ha] using he
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases ha : a.getLsbD i = true
    · have hb := (mem_decodeTyped b ⟨i,hi⟩).1 (h ((mem_decodeTyped a ⟨i,hi⟩).2 ha))
      simp [ha,hb]
    · have hf : a.getLsbD i = false := Bool.eq_false_iff.mpr ha
      simp [hf]

/-- The alphabet overapproximation is obtained from a represented literal row,
not from a digest or a producer-declared possible-block set. -/
theorem represented_block_in_alphabet (d : CodedDomain) (P : Family Point)
    (represented : ∃ p ∈ d.supported.domain.2, RepresentsPencil p P)
    (B : Finset Point) (hB : B ∈ P) : encodeTyped B ∈ d.alphabet := by
  obtain ⟨p,hp,hrep⟩ := represented
  obtain ⟨cs,hcs,rfl⟩ := List.mem_map.mp hp
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hcs
  have hd := (represents_decode_iff (d.pencil r) P).1 hrep
  rw [← hd] at hB
  obtain ⟨c,hc,hcB⟩ := List.mem_map.mp (List.mem_toFinset.mp hB)
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
  have he : encodeTyped B = d.alphabet[i] := by rw [← hcB,encode_decodeTyped]
  rw [he]
  exact List.getElem_mem _

end C13.Enumeration.Census
