import C13Enumeration.Census.CoverRows

namespace C13.Enumeration.Census
open Finset C13.Checker.RawSupport C13.SourceData
set_option Elab.async false
set_option maxRecDepth 10000

def FixedHolds (chosen : Finset Code) (fixed : List (Code × Bool)) : Prop :=
  ∀ x ∈ fixed, (x.1 ∈ chosen ↔ x.2 = true)

def ValidRow (K : Family Point) (Q : Finset Point)
    (fixed : List (Code × Bool)) (r : LinearRow) : Prop :=
  match r.test with
  | .covers t => 0 ≤ r.weight ∧ r.demand = 1 ∧
      decodeTyped t ⊆ univ.erase hole ∧ (decodeTyped t).card = 4 ∧
      ∀ B ∈ K, ¬ decodeTyped t ⊆ B
  | .incident q => q ∈ Q ∧ r.demand = (15 - degree K q : Nat)
  | .block b => ∃ v : Bool, (b,v) ∈ fixed ∧ r.demand = (if v then 1 else 0)

theorem incident_count (F : Family Point) (q : Point) :
    ((outsideCodes F).filter (fun b => b.getLsbD q.val = true)).card =
      (pencil F hole q).card := by
  rw [outsideCodes,filter_image,card_image_of_injective _ encodeTyped_injective]
  congr 1
  ext B
  have hi : (encodeTyped B).getLsbD q.val = true ↔ q ∈ B := by
    rw [← mem_decodeTyped,decode_encodeTyped]
  simp only [mem_filter,mem_outside,mem_pencil,hi]
  tauto

theorem block_count (chosen : Finset Code) (b : Code) :
    ((chosen.filter fun c => (c == b) = true).card : Int) =
      (if b ∈ chosen then 1 else 0) := by
  have hh : (chosen.filter fun c => (c == b) = true) =
      (if b ∈ chosen then {b} else ∅) := by
    ext c
    by_cases hb : b ∈ chosen <;> simp_all
    intro hc he
    subst c
    exact hb hc
  rw [hh]
  split <;> simp_all

theorem valid_row_satisfied (F K : Family Point) (Q : Finset Point)
    (hcover : IsCoverOn univ F 7 4) (hroot : link F hole = K)
    (hQ : Q ⊆ univ.erase hole)
    (hmin : ∀ q ∈ Q, degree F q = 15)
    (fixed : List (Code × Bool)) (hfixed : FixedHolds (outsideCodes F) fixed)
    (r : LinearRow) (valid : ValidRow K Q fixed r) : r.Satisfied (outsideCodes F) := by
  rcases r with ⟨test,demand,weight⟩
  cases test with
  | covers t =>
    obtain ⟨hw,hd,hT,hcard,hu⟩ := valid
    change demand = 1 at hd
    right
    refine ⟨hw,?_⟩
    obtain ⟨B,hBF,hTB⟩ := required_quad_covered_outside F K hcover hroot
      (decodeTyped t) hT hcard hu
    have hb : encodeTyped B ∈ (outsideCodes F).filter (fun b => subsetB t b = true) := by
      refine mem_filter.mpr ⟨mem_image.mpr ⟨B,hBF,rfl⟩,?_⟩
      apply (subsetB_iff ..).2
      simpa using hTB
    have hc : 0 < ((outsideCodes F).filter (fun b => subsetB t b = true)).card :=
      card_pos.mpr ⟨_,hb⟩
    change demand ≤ (((outsideCodes F).filter (fun b => subsetB t b = true)).card : Int)
    rw [hd]
    exact_mod_cast hc
  | incident q =>
    obtain ⟨hq,hd⟩ := valid
    left
    have hqr : q ≠ hole := (mem_erase.mp (hQ hq)).1
    have hc := pencil_card_add_root_degree F hole q hqr
    rw [hroot,hmin q hq] at hc
    have hp : (pencil F hole q).card = 15 - degree K q := by omega
    change demand = (((outsideCodes F).filter (fun b => b.getLsbD q.val = true)).card : Int)
    rw [incident_count,hp]
    exact hd
  | block b =>
    obtain ⟨v,hv,hd⟩ := valid
    change demand = (if v then (1 : Int) else 0) at hd
    left
    change demand = (((outsideCodes F).filter (fun c => (c == b) = true)).card : Int)
    rw [block_count,hd]
    have hh := hfixed (b,v) hv
    cases v <;> simp_all

end C13.Enumeration.Census
