import C13Arc.Transport

/-! Explicit refutation certificates. Python may suggest the tree; every
case split, incompatible choice, and budget cut is checked in Lean. -/
namespace C13.Checker.Arc

inductive Refutation where
  | close
  | split (children : List Refutation)
  deriving Repr

/-- Exact arity is checked, so omitting a difficult branch cannot validate. -/
def zipAllExact {A B : Type} (f : A → B → Bool) : List A → List B → Bool
  | [], [] => true
  | a::as, b::bs => f a b && zipAllExact f as bs
  | _, _ => false

theorem zipAllExact_covers {A B : Type} (f : A → B → Bool) (as : List A) (bs : List B)
    (h : zipAllExact f as bs = true) : ∀ a ∈ as, ∃ b ∈ bs, f a b = true := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih =>
    cases bs with
    | nil => simp [zipAllExact] at h
    | cons b bs =>
      have hh : f a b = true ∧ zipAllExact f as bs = true := by
        simpa [zipAllExact] using h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨b, by simp, hh.1⟩
      · obtain ⟨y,hy,hf⟩ := ih bs hh.2 x hx
        exact ⟨y, by simp [hy], hf⟩

/-- A leaf is valid only for an over-budget union or an empty next domain.
A split accounts for every literal candidate in the next domain. -/
def refutationB (budget : Nat) : List Domain → Selected → Refutation → Bool
  | [], chosen, _ => !decide (WithinBudget budget chosen)
  | (_,ps)::_, chosen, .close =>
    !decide (WithinBudget budget chosen) || ps.isEmpty
  | (q,ps)::ds, chosen, .split cs =>
    zipAllExact (fun p c => !decide (CompatibleWith chosen q p) ||
      refutationB budget ds ((q,p)::chosen) c) ps cs

theorem refutation_sound (budget : Nat) (ds : List Domain) (chosen : Selected)
    (cert : Refutation) (checked : refutationB budget ds chosen cert = true) :
    ¬ HasJoin budget ds chosen := by
  induction ds generalizing chosen cert with
  | nil => simpa [refutationB, HasJoin] using checked
  | cons d ds ih =>
    rcases d with ⟨q,ps⟩
    cases cert with
    | close =>
      have hh : ¬ WithinBudget budget chosen ∨ ps = [] := by
        simpa [refutationB] using checked
      intro hj
      rcases hh with hbudget | hempty
      · exact hbudget hj.withinBudget
      · obtain ⟨p,hp,_,_⟩ := hj
        simp [hempty] at hp
    | split cs =>
      intro hj
      obtain ⟨p,hp,hcomp,hrest⟩ := hj
      obtain ⟨c,_,hc⟩ := zipAllExact_covers _ ps cs checked p hp
      have hr : refutationB budget ds ((q,p)::chosen) c = true := by
        simpa [hcomp] using hc
      exact ih _ c hr hrest

/-- The original tuple may survive only jointly, never by individual raw
candidate inclusion. Transport and certificate checking are distinct premises. -/
theorem no_jointWitness_of_arc_certificate {budget rounds : Nat}
    {raw residual : List Domain} (cert : Refutation)
    (transport : arcRounds rounds raw = residual)
    (checked : refutationB budget residual [] cert = true) :
    ∀ pick, ¬ JointWitness budget raw pick := by
  intro pick h
  have hs := witness_survives_rounds rounds h
  rw [transport] at hs
  exact refutation_sound budget residual [] cert checked (hasJoin_of_jointWitness hs)

end C13.Checker.Arc
