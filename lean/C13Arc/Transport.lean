import C13.Checker

/-! A chosen jointly compatible tuple survives synchronous arc pruning.
This does not assert individual inclusion of the whole raw domain after pruning. -/
namespace C13.Checker.Arc
abbrev Choice := Nat → Pencil

def ChosenFrom (ds : List Domain) (pick : Choice) : Prop :=
  ∀ d ∈ ds, pick d.1 ∈ d.2

def JointCompatible (ds : List Domain) (pick : Choice) : Prop :=
  ∀ d ∈ ds, ∀ e ∈ ds, Compatible d.1 (pick d.1) e.1 (pick e.1)

def selectedOf (ds : List Domain) (pick : Choice) : Selected :=
  ds.map fun d => (d.1, pick d.1)

def JointWitness (budget : Nat) (ds : List Domain) (pick : Choice) : Prop :=
  ChosenFrom ds pick ∧ JointCompatible ds pick ∧ WithinBudget budget (selectedOf ds pick)

/-- Skip the same point, as in the reviewed synchronous arc filter. -/
def supportedB (q : Nat) (p : Pencil) (other : Domain) : Bool :=
  if q = other.1 then true
  else other.2.any fun s => decide (Compatible q p other.1 s)

def keepB (ds : List Domain) (d : Domain) (p : Pencil) : Bool :=
  ds.all fun other => supportedB d.1 p other

def arcStep (ds : List Domain) : List Domain :=
  ds.map fun d => (d.1, d.2.filter (keepB ds d))

theorem supportedB_of_joint {ds : List Domain} {pick : Choice}
    (hc : ChosenFrom ds pick) (hj : JointCompatible ds pick)
    {d e : Domain} (hd : d ∈ ds) (he : e ∈ ds) :
    supportedB d.1 (pick d.1) e = true := by
  unfold supportedB
  split
  · rfl
  · exact List.any_eq_true.mpr ⟨pick e.1, hc e he, decide_eq_true (hj d hd e he)⟩

theorem chosen_survives_step {ds : List Domain} {pick : Choice}
    (hc : ChosenFrom ds pick) (hj : JointCompatible ds pick) :
    ChosenFrom (arcStep ds) pick := by
  intro e he
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp he
  exact List.mem_filter.mpr ⟨hc d hd, List.all_eq_true.mpr fun other ho =>
    supportedB_of_joint hc hj hd ho⟩

theorem joint_survives_step {ds : List Domain} {pick : Choice}
    (hj : JointCompatible ds pick) : JointCompatible (arcStep ds) pick := by
  intro d hd e he
  obtain ⟨d₀,hd₀,rfl⟩ := List.mem_map.mp hd
  obtain ⟨e₀,he₀,rfl⟩ := List.mem_map.mp he
  exact hj d₀ hd₀ e₀ he₀

/-- Candidate deletion changes no selected physical pencil. -/
theorem selectedOf_arcStep (ds : List Domain) (pick : Choice) :
    selectedOf (arcStep ds) pick = selectedOf ds pick := by
  simp [selectedOf, arcStep, List.map_map, Function.comp_def]

theorem witness_survives_step {budget : Nat} {ds : List Domain} {pick : Choice}
    (h : JointWitness budget ds pick) : JointWitness budget (arcStep ds) pick := by
  refine ⟨chosen_survives_step h.1 h.2.1, joint_survives_step h.2.1, ?_⟩
  rw [selectedOf_arcStep]
  exact h.2.2

/-- Fixed many rounds, without trusting a stopping heuristic. -/
def arcRounds : Nat → List Domain → List Domain
  | 0, ds => ds
  | n+1, ds => arcStep (arcRounds n ds)

theorem witness_survives_rounds {budget : Nat} {ds : List Domain} {pick : Choice}
    (n : Nat) (h : JointWitness budget ds pick) :
    JointWitness budget (arcRounds n ds) pick := by
  induction n with
  | zero => exact h
  | succ n ih => exact witness_survives_step ih

theorem unionBlocks_move (front chosen : Selected) (q : Nat) (p : Pencil) :
    unionBlocks (front ++ (q,p) :: chosen) = unionBlocks ((q,p) :: front ++ chosen) := by
  apply Finset.ext
  intro b
  simp only [unionBlocks, List.flatMap_append, List.flatMap_cons,
    List.mem_toFinset, List.mem_append]
  tauto

theorem hasJoin_of_choice_aux (budget : Nat) (ds : List Domain) (pick : Choice)
    (chosen : Selected) (hc : ChosenFrom ds pick) (hj : JointCompatible ds pick)
    (hprev : ∀ d ∈ ds, CompatibleWith chosen d.1 (pick d.1))
    (hb : WithinBudget budget (selectedOf ds pick ++ chosen)) :
    HasJoin budget ds chosen := by
  induction ds generalizing chosen with
  | nil => simpa [HasJoin, selectedOf] using hb
  | cons d ds ih =>
    rcases d with ⟨q,ps⟩
    refine ⟨pick q, hc (q,ps) (by simp), hprev (q,ps) (by simp), ?_⟩
    apply ih ((q,pick q)::chosen)
    · intro e he
      exact hc e (by simp [he])
    · intro e he f hf
      exact hj e (by simp [he]) f (by simp [hf])
    · intro e he x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hj e (by simp [he]) (q,ps) (by simp)
      · exact hprev e (by simp [he]) x hx
    · unfold WithinBudget at *
      rw [unionBlocks_move]
      simpa [selectedOf] using hb

theorem hasJoin_of_jointWitness {budget : Nat} {ds : List Domain} {pick : Choice}
    (h : JointWitness budget ds pick) : HasJoin budget ds [] := by
  apply hasJoin_of_choice_aux budget ds pick [] h.1 h.2.1
  · intro d hd x hx
    simp at hx
  · simpa using h.2.2

/-- False residual checking rejects every original JOINT witness once actual
rounds are linked to the residual. Raw-domain completeness remains separate. -/
theorem no_jointWitness_of_pruned_check {budget rounds : Nat} {raw residual : List Domain}
    (transport : arcRounds rounds raw = residual)
    (checked : hasJoinPrunedB budget residual [] = false) :
    ∀ pick, ¬ JointWitness budget raw pick := by
  intro pick hw
  have hs := witness_survives_rounds rounds hw
  rw [transport] at hs
  exact noJoin_of_pruned_check budget residual checked (hasJoin_of_jointWitness hs)
/-- Conversely, a surviving candidate is still a member of its raw domain. -/
theorem witness_before_step {budget : Nat} {ds : List Domain} {pick : Choice}
    (h : JointWitness budget (arcStep ds) pick) : JointWitness budget ds pick := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    have hm : (d.1, d.2.filter (keepB ds d)) ∈ arcStep ds :=
      List.mem_map.mpr ⟨d,hd,rfl⟩
    exact (List.mem_filter.mp (h.1 _ hm)).1
  · intro d hd e he
    exact h.2.1 (d.1,d.2.filter (keepB ds d)) (List.mem_map.mpr ⟨d,hd,rfl⟩)
      (e.1,e.2.filter (keepB ds e)) (List.mem_map.mpr ⟨e,he,rfl⟩)
  · simpa only [selectedOf_arcStep] using h.2.2

theorem witness_step_iff {budget : Nat} {ds : List Domain} {pick : Choice} :
    JointWitness budget (arcStep ds) pick ↔ JointWitness budget ds pick :=
  ⟨witness_before_step, witness_survives_step⟩

theorem witness_rounds_iff {budget : Nat} {ds : List Domain} {pick : Choice} (n : Nat) :
    JointWitness budget (arcRounds n ds) pick ↔ JointWitness budget ds pick := by
  induction n with
  | zero => rfl
  | succ n ih => exact witness_step_iff.trans ih

@[simp] theorem arcStep_labels (ds : List Domain) :
    (arcStep ds).map Prod.fst = ds.map Prod.fst := by
  simp [arcStep, List.map_map, Function.comp_def]

@[simp] theorem arcRounds_labels (ds : List Domain) (n : Nat) :
    (arcRounds n ds).map Prod.fst = ds.map Prod.fst := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [arcRounds, arcStep_labels] using ih

end C13.Checker.Arc
