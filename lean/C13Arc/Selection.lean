import C13Arc.Certificate

/-! Direct transport for the existing HasJoin semantics. Distinct domain labels
let a literal tuple be represented by one pencil-valued choice function. -/
namespace C13.Checker.Arc

def ChosenList : List Domain → Selected → Prop
  | [], [] => True
  | (q,ps)::ds, (r,p)::xs => r = q ∧ p ∈ ps ∧ ChosenList ds xs
  | _, _ => False

def AllCompatible (xs : Selected) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ xs, Compatible x.1 x.2 y.1 y.2

theorem hasJoin_selected (budget : Nat) (ds : List Domain) (chosen : Selected)
    (h : HasJoin budget ds chosen) :
    ∃ xs, ChosenList ds xs ∧ AllCompatible xs ∧
      (∀ x ∈ xs, CompatibleWith chosen x.1 x.2) ∧
      WithinBudget budget (xs ++ chosen) := by
  induction ds generalizing chosen with
  | nil => exact ⟨[], trivial, by simp [AllCompatible], by simp, h⟩
  | cons d ds ih =>
    rcases d with ⟨q,ps⟩
    obtain ⟨p,hp,hcomp,hrest⟩ := h
    obtain ⟨xs,hxs,hpair,hprev,hbudget⟩ := ih _ hrest
    refine ⟨(q,p)::xs, ⟨rfl,hp,hxs⟩, ?_, ?_, ?_⟩
    · intro x hx y hy
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases List.mem_cons.mp hy with rfl | hy
        · rfl
        · exact (hprev y hy (q,p) (by simp)).symm
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact hprev x hx (q,p) (by simp)
        · exact hpair x hx y hy
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hcomp
      · intro y hy
        exact hprev x hx y (by simp [hy])
    · unfold WithinBudget at *
      rw [unionBlocks_move] at hbudget
      exact hbudget

def choiceOf : Selected → Choice
  | [], _ => []
  | (q,p)::xs, r => if r = q then p else choiceOf xs r

theorem choiceOf_mem (xs : Selected) (hn : (xs.map Prod.fst).Nodup)
    (x : Nat × Pencil) (hx : x ∈ xs) : choiceOf xs x.1 = x.2 := by
  induction xs generalizing x with
  | nil => simp at hx
  | cons a xs ih =>
    rcases a with ⟨q,p⟩
    have hh : q ∉ xs.map Prod.fst ∧ (xs.map Prod.fst).Nodup := by
      simpa using hn
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [choiceOf]
    · have hneq : x.1 ≠ q := by
        intro hq
        exact hh.1 (List.mem_map.mpr ⟨x,hx,hq⟩)
      simpa [choiceOf, hneq] using ih hh.2 x hx

theorem chosenList_labels {ds : List Domain} {xs : Selected} (h : ChosenList ds xs) :
    xs.map Prod.fst = ds.map Prod.fst := by
  induction ds generalizing xs with
  | nil => cases xs <;> simp_all [ChosenList]
  | cons d ds ih =>
    cases xs with
    | nil => simp [ChosenList] at h
    | cons x xs =>
      rcases d with ⟨q,ps⟩
      rcases x with ⟨r,p⟩
      obtain ⟨he,_,ht⟩ := h
      subst r
      simpa using congrArg (List.cons q) (ih ht)

theorem chosenList_member {ds : List Domain} {xs : Selected} (h : ChosenList ds xs)
    (d : Domain) (hd : d ∈ ds) :
    ∃ x ∈ xs, x.1 = d.1 ∧ x.2 ∈ d.2 := by
  induction ds generalizing xs with
  | nil => simp at hd
  | cons e ds ih =>
    cases xs with
    | nil => simp [ChosenList] at h
    | cons x xs =>
      rcases e with ⟨q,ps⟩
      rcases x with ⟨r,p⟩
      obtain ⟨heq,hp,ht⟩ := h
      subst r
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨(q,p), by simp, rfl, hp⟩
      · obtain ⟨y,hy,he,hp⟩ := ih ht hd
        exact ⟨y, by simp [hy], he, hp⟩

theorem selectedOf_eq_chosen {ds : List Domain} {xs : Selected} (h : ChosenList ds xs)
    (pick : Choice) (values : ∀ x ∈ xs, pick x.1 = x.2) : selectedOf ds pick = xs := by
  induction ds generalizing xs with
  | nil => cases xs <;> simp_all [ChosenList, selectedOf]
  | cons d ds ih =>
    cases xs with
    | nil => simp [ChosenList] at h
    | cons x xs =>
      rcases d with ⟨q,ps⟩
      rcases x with ⟨r,p⟩
      obtain ⟨he,_,ht⟩ := h
      subst r
      have hv : pick q = p := values (q,p) (by simp)
      have htail : selectedOf ds pick = xs := ih ht (fun y hy => values y (by simp [hy]))
      simpa [selectedOf, hv] using congrArg (List.cons (q,p)) htail

theorem exists_jointWitness_of_hasJoin {budget : Nat} {ds : List Domain}
    (labels : (ds.map Prod.fst).Nodup) (h : HasJoin budget ds []) :
    ∃ pick, JointWitness budget ds pick := by
  obtain ⟨xs,hsel,hcompat,_,hb⟩ := hasJoin_selected budget ds [] h
  have hlabels : (xs.map Prod.fst).Nodup := by rw [chosenList_labels hsel]; exact labels
  let pick := choiceOf xs
  have hv : ∀ x ∈ xs, pick x.1 = x.2 := choiceOf_mem xs hlabels
  refine ⟨pick, ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨x,hx,he,hp⟩ := chosenList_member hsel d hd
    rw [← he, hv x hx]
    exact hp
  · intro d hd e he
    obtain ⟨x,hx,hxq,_⟩ := chosenList_member hsel d hd
    obtain ⟨y,hy,hyq,_⟩ := chosenList_member hsel e he
    rw [← hxq, ← hyq, hv x hx, hv y hy]
    exact hcompat x hx y hy
  · rw [selectedOf_eq_chosen hsel pick hv]
    simpa using hb

theorem hasJoin_iff_jointWitness {budget : Nat} {ds : List Domain}
    (labels : (ds.map Prod.fst).Nodup) :
    HasJoin budget ds [] ↔ ∃ pick, JointWitness budget ds pick :=
  ⟨exists_jointWitness_of_hasJoin labels, fun ⟨_,h⟩ => hasJoin_of_jointWitness h⟩

theorem hasJoin_survives_rounds {budget : Nat} {ds : List Domain}
    (labels : (ds.map Prod.fst).Nodup) (rounds : Nat) (h : HasJoin budget ds []) :
    HasJoin budget (arcRounds rounds ds) [] := by
  obtain ⟨pick,hpick⟩ := exists_jointWitness_of_hasJoin labels h
  exact hasJoin_of_jointWitness (witness_survives_rounds rounds hpick)

/-- Complete necessary-direction transport for distinct labeled domains. The
original domains still need the independent mathematical completeness argument. -/
theorem noJoin_of_arc_certificate {budget rounds : Nat} {raw residual : List Domain}
    (labels : (raw.map Prod.fst).Nodup) (cert : Refutation)
    (transport : arcRounds rounds raw = residual)
    (checked : refutationB budget residual [] cert = true) : ¬ HasJoin budget raw [] := by
  intro h
  have hs := hasJoin_survives_rounds labels rounds h
  rw [transport] at hs
  exact refutation_sound budget residual [] cert checked hs
/-- Synchronous arc pruning is an exact transformation of the existing join
semantics when point labels are distinct, including at a nonterminal frontier. -/
theorem hasJoin_rounds_iff {budget : Nat} {ds : List Domain}
    (labels : (ds.map Prod.fst).Nodup) (rounds : Nat) :
    HasJoin budget (arcRounds rounds ds) [] ↔ HasJoin budget ds [] := by
  have reducedLabels : ((arcRounds rounds ds).map Prod.fst).Nodup := by simpa using labels
  rw [hasJoin_iff_jointWitness reducedLabels, hasJoin_iff_jointWitness labels]
  exact exists_congr fun _ => witness_rounds_iff rounds

end C13.Checker.Arc
