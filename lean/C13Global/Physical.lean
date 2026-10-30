import C13Global.EmptyCore
import C13Global.Nonincident
import C13Global.CoverRows
import C13Enumeration.Census.BlockUniverse

namespace C13.Global
open Finset C13.SourceData C13.Checker.RawSupport C13.Enumeration C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem blockUniverse_eq : blockUniverse = blockCodes := by decide +kernel

theorem blockUniverse_complete (F : Family Point) (hcover : IsCoverOn univ F 7 4)
    (B : Finset Point) (hB : B ∈ outside F hole) : encodeTyped B ∈ blockUniverse := by
  rw [blockUniverse_eq]
  obtain ⟨hBF,holeB⟩ := mem_outside.mp hB
  apply encode_mem_blockCodes B
  · intro p hp
    exact mem_erase.mpr ⟨by intro he; subst p; exact holeB hp,mem_univ _⟩
  · exact (hcover.1 B hBF).2

def AlphabetComplete (K : Family Point) (alphabets : List Mask) : Prop :=
  ∀ q : Point, q ≠ hole → ∀ P ∈ completeDomain catalog hole K hole q,
    ∀ B ∈ P, (alphabets.getD q.val 0).testBit (encodeTyped B).toNat = true

def NonincidentComplete (alphabets : List Mask) : Prop :=
  ∀ q : Point, q ≠ hole → ∀ b ∈ blockUniverse, b.getLsbD q.val = false →
    (alphabets.getD q.val 0).testBit b.toNat = true

theorem actual_support (K : Family Point) (alphabets : List Mask)
    (halph : AlphabetComplete K alphabets) (hnon : NonincidentComplete alphabets)
    (hclass : ClassifiesMinimumLinks catalog hole)
    (F : Family Point) (hcover : IsCoverOn univ F 7 4) (hroot : link F hole = K)
    (q : Point) (hq : q ≠ hole) (hmin : degree F q = 15)
    (B : Finset Point) (hB : B ∈ outside F hole) :
    (alphabets.getD q.val 0).testBit (encodeTyped B).toNat = true := by
  cases hbit : (encodeTyped B).getLsbD q.val with
  | false => exact hnon q hq _ (blockUniverse_complete F hcover B hB) hbit
  | true =>
    have hp : pencil F hole q ∈ completeDomain catalog hole K hole q := by
      rw [← hroot]
      exact actual_pencil_mem_completeDomain catalog hole hclass F hcover hq hmin
    apply halph q hq (pencil F hole q) hp B
    obtain ⟨hBF,holeB⟩ := mem_outside.mp hB
    refine mem_pencil.mpr ⟨hBF,holeB,?_⟩
    have hh := (mem_decodeTyped (encodeTyped B) q).2 hbit
    simpa using hh

def TargetPhysicalValid (t : Target) : Prop :=
  decodeTyped t.quad ⊆ univ.erase hole ∧ (decodeTyped t.quad).card = 4

instance (t : Target) : Decidable (TargetPhysicalValid t) := by
  unfold TargetPhysicalValid
  infer_instance

-- Every target's geometric interpretation is checked, separately from mask arithmetic.
theorem targets_physical_checked : targetList.all (fun t => decide (TargetPhysicalValid t)) = true := by decide +kernel

theorem target_physical (i : Fin 141) : TargetPhysicalValid (targetAt i) :=
  of_decide_eq_true (List.all_eq_true.mp targets_physical_checked _ (List.getElem_mem _))

theorem empty_actual_obstruction (K : Family Point) (root : List Code)
    (root_binding : decodeSource root = K) (alphabets : List Mask)
    (halph : AlphabetComplete K alphabets) (hnon : NonincidentComplete alphabets)
    (c : EmptyCase) (checked : emptyCheckB root alphabets c = true)
    (hclass : ClassifiesMinimumLinks catalog hole)
    (F : Family Point) (hcover : IsCoverOn univ F 7 4) (hroot : link F hole = K)
    (hpoints : ∀ q ∈ c.1, q ≠ hole) (hmin : ∀ q ∈ c.1, degree F q = 15) : False := by
  have hu : rootUncoveredB root (targetAt c.2).quad = true := by
    have hh := checked
    simp only [emptyCheckB,Bool.and_eq_true] at hh
    exact hh.1
  obtain ⟨hT,hcard⟩ := target_physical c.2
  have hunc : ∀ A ∈ K, ¬ decodeTyped (targetAt c.2).quad ⊆ A := by
    intro A hA hs
    rw [← root_binding] at hA
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hA)
    have hn := rootUncovered_sound root _ hu b hb
    have hy := (C13.Enumeration.Census.subsetB_iff _ _).2 hs
    change subsetB (targetAt c.2).quad b = true at hy
    rw [hn] at hy
    contradiction
  obtain ⟨B,hBF,hTB⟩ := required_quad_covered_outside F K hcover hroot _ hT hcard hunc
  have hs := emptyCheck_sound root alphabets c checked (encodeTyped B)
    (blockUniverse_complete F hcover B hBF)
    (fun q hq => actual_support K alphabets halph hnon hclass F hcover hroot q
      (hpoints q hq) (hmin q hq) B hBF)
  have ht : C13.Enumeration.Census.subsetB (targetAt c.2).quad (encodeTyped B) = true := by
    apply (C13.Enumeration.Census.subsetB_iff _ _).2
    simpa using hTB
  change subsetB (targetAt c.2).quad (encodeTyped B) = true at ht
  rw [hs] at ht
  contradiction

theorem nonincident_complete_of_check (alphabets : List Mask)
    (checked : (List.finRange 13).all (fun q => if q = hole then true else
      decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true) :
    NonincidentComplete alphabets := by
  intro q hq b hb hbit
  have hh := List.all_eq_true.mp checked q (by simp)
  simp only [hq,if_false,decide_eq_true_eq] at hh
  exact mask_subset _ _ hh b (nonincident_bit q b hb hbit)

end C13.Global
