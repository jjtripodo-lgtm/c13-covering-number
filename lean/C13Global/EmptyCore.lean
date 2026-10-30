import C13Global.Targets
namespace C13.Global
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev EmptyCase := List Point × Fin 141

def subsetB (a b : Code) : Bool := (a &&& b) == a

def rootUncoveredB (root : List Code) (quad : Code) : Bool :=
  root.all (fun b => !(subsetB quad b))

def emptyCheckB (root : List Code) (alphabets : List Mask) (c : EmptyCase) : Bool :=
  rootUncoveredB root (targetAt c.2).quad &&
    decide (restrictMask universeMask alphabets c.1 &&& (targetAt c.2).mask = 0)

theorem rootUncovered_sound (root : List Code) (quad : Code)
    (checked : rootUncoveredB root quad = true) :
    ∀ b ∈ root, subsetB quad b = false := by
  intro b hb
  have h := List.all_eq_true.mp checked b hb
  simpa only [Bool.not_eq_true'] using h

/-- A kernel checked certificate excludes every block in the complete universe;
no producer flag or enumeration claim is used to prune that universe. -/
theorem emptyCheck_sound (root : List Code) (alphabets : List Mask) (c : EmptyCase)
    (checked : emptyCheckB root alphabets c = true)
    (b : Code) (hb : b ∈ blockUniverse)
    (supported : ∀ q ∈ c.1, (alphabets.getD q.val 0).testBit b.toNat = true) :
    subsetB (targetAt c.2).quad b = false := by
  have hh : rootUncoveredB root (targetAt c.2).quad = true ∧
      restrictMask universeMask alphabets c.1 &&& (targetAt c.2).mask = 0 := by
    simpa only [emptyCheckB,Bool.and_eq_true,decide_eq_true_eq] using checked
  have hbase : universeMask.testBit b.toNat = true := by
    rw [← universeMask_checked,listMask_bit]
    simpa only [decide_eq_true_eq] using hb
  have hs := restrictMask_bit universeMask alphabets c.1 b hbase supported
  cases ht : subsetB (targetAt c.2).quad b with
  | false => rfl
  | true =>
    have hm : b ∈ blockUniverse.filter (fun b => ((targetAt c.2).quad &&& b) == (targetAt c.2).quad) :=
      List.mem_filter.mpr ⟨hb,ht⟩
    have htmask : ((targetAt c.2).mask).testBit b.toNat = true := by
      rw [← targetAt_valid,listMask_bit]
      simpa only [decide_eq_true_eq] using hm
    exact (masks_disjoint _ _ hh.2 b hs htmask).elim

/-- The finite table is verified one entry at a time. Coverage of larger point
sets is handled separately by an explicit subset witness. -/
theorem emptyChecks_sound (root : List Code) (alphabets : List Mask)
    (cases : List EmptyCase) (checked : cases.all (emptyCheckB root alphabets) = true)
    (c : EmptyCase) (hc : c ∈ cases) :
    rootUncoveredB root (targetAt c.2).quad = true ∧
    ∀ b ∈ blockUniverse,
      (∀ q ∈ c.1, (alphabets.getD q.val 0).testBit b.toNat = true) →
      subsetB (targetAt c.2).quad b = false := by
  have h := List.all_eq_true.mp checked c hc
  refine ⟨?_,fun b hb hs => emptyCheck_sound root alphabets c h b hb hs⟩
  have hh := h
  simp only [emptyCheckB,Bool.and_eq_true] at hh
  exact hh.1

def emptyCoversB (cases : List EmptyCase) (points : List Point) : Bool :=
  cases.any (fun c => c.1.all (fun q => points.contains q))

theorem emptyCovers_sound (cases : List EmptyCase) (points : List Point)
    (checked : emptyCoversB cases points = true) :
    ∃ c ∈ cases, ∀ q ∈ c.1, q ∈ points := by
  obtain ⟨c,hc,hall⟩ := List.any_eq_true.mp checked
  refine ⟨c,hc,?_⟩
  intro q hq
  exact List.contains_iff.mp (List.all_eq_true.mp hall q hq)

end C13.Global
