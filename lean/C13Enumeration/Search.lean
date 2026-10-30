import C13RawStarRecovery.CenterDomains

/-! A generic executable bijection backtracker. Its pruning contract ranges over
all unfinished points, including points absent from every incidence block. -/
namespace C13.Enumeration
variable {α β γ : Type*} [DecidableEq α] [DecidableEq β]

/-- Nondependent table update avoids proof casts in kernel computation. -/
def put (f : α → β) (a : α) (b : β) (x : α) : β := if x = a then b else f x

@[simp] theorem put_same (f : α → β) (a : α) (b : β) : put f a b a = b := by simp [put]
@[simp] theorem put_ne (f : α → β) (a : α) (b : β) {x : α} (h : x ≠ a) :
    put f a b x = f x := by simp [put,h]

/-- The partial table already agrees with its full extension off the work list. -/
def AgreesOff (remaining : List α) (f e : α → β) : Prop :=
  ∀ x, x ∉ remaining → f x = e x

/-- Candidate images are removed immediately. A false prefix predicate prunes
an entire subtree; the final emitter determines the observable output. -/
def search (prune : List α → (α → β) → Bool) (finish : (α → β) → List γ) :
    List α → List β → (α → β) → List γ
  | [], _, f => if prune [] f then finish f else []
  | x :: xs, ys, f => if prune (x :: xs) f then
      ys.flatMap (fun y => search prune finish xs (ys.erase y) (put f x y))
    else []

/-- Soundness needs no faith in the producer or in its pruning heuristic: every
emitted result is accepted by the exact leaf emitter. -/
theorem search_sound (prune : List α → (α → β) → Bool)
    (finish : (α → β) → List γ) (xs : List α) (ys : List β) (f : α → β)
    (z : γ) (hz : z ∈ search prune finish xs ys f) :
    ∃ g, z ∈ finish g := by
  induction xs generalizing ys f with
  | nil =>
    simp only [search] at hz
    split at hz
    · exact ⟨f,hz⟩
    · simp at hz
  | cons x xs ih =>
    simp only [search] at hz
    split at hz
    · obtain ⟨y,hy,hz⟩ := List.mem_flatMap.mp hz
      exact ih _ _ hz
    · simp at hz

/-- Completeness for every injective full extension. No group, support, or
incidence assumption restricts which source labels must be assigned. -/
theorem search_complete (prune : List α → (α → β) → Bool)
    (finish : (α → β) → List γ) (e : α → β) (he : Function.Injective e)
    (hprune : ∀ xs f, AgreesOff xs f e → prune xs f = true)
    (xs : List α) (ys : List β) (f : α → β) (hn : xs.Nodup)
    (hy : ∀ x ∈ xs, e x ∈ ys) (hf : AgreesOff xs f e)
    (z : γ) (hz : z ∈ finish e) :
    z ∈ search prune finish xs ys f := by
  induction xs generalizing ys f with
  | nil =>
    have hfe : f = e := funext fun x => hf x (by simp)
    subst f
    simpa [search,hprune [] e hf] using hz
  | cons x xs ih =>
    rw [search,if_pos (hprune (x :: xs) f hf)]
    apply List.mem_flatMap.mpr
    refine ⟨e x,hy x (by simp),?_⟩
    apply ih (ys.erase (e x)) (put f x (e x)) hn.of_cons
    · intro a ha
      have hax : a ≠ x := by
        intro h
        subst a
        exact (List.nodup_cons.mp hn).1 ha
      exact (List.mem_erase_of_ne (fun h => hax (he h))).mpr (hy a (by simp [ha]))
    · intro a ha
      by_cases hax : a = x
      · subst a
        simp
      · rw [put_ne _ _ _ hax]
        exact hf a (by simp [hax,ha])

/-- A safe necessary-condition prune can be intersected with another one. -/
theorem safe_prune_and (p q : List α → (α → β) → Bool) (e : α → β)
    (hp : ∀ xs f, AgreesOff xs f e → p xs f = true)
    (hq : ∀ xs f, AgreesOff xs f e → q xs f = true) :
    ∀ xs f, AgreesOff xs f e → (p xs f && q xs f) = true := by
  intro xs f hf
  simp [hp xs f hf,hq xs f hf]
end C13.Enumeration

namespace C13.Enumeration
variable {α β γ : Type*} [DecidableEq α] [DecidableEq β]

/-- Incremental form: inspect only the new assignment against the prefix. -/
def assignSearch (step : List α → (α → β) → α → β → Bool)
    (finish : (α → β) → List γ) : List α → List β → (α → β) → List γ
  | [], _, f => finish f
  | x :: xs, ys, f => ys.flatMap fun y =>
      if step (x :: xs) f x y then
        assignSearch step finish xs (ys.erase y) (put f x y)
      else []

theorem assignSearch_sound (step : List α → (α → β) → α → β → Bool)
    (finish : (α → β) → List γ) (xs : List α) (ys : List β) (f : α → β)
    (z : γ) (hz : z ∈ assignSearch step finish xs ys f) :
    ∃ g, z ∈ finish g := by
  induction xs generalizing ys f with
  | nil => exact ⟨f,hz⟩
  | cons x xs ih =>
    obtain ⟨y,hy,hz⟩ := List.mem_flatMap.mp hz
    split at hz
    · exact ih _ _ hz
    · simp at hz

theorem assignSearch_complete (step : List α → (α → β) → α → β → Bool)
    (finish : (α → β) → List γ) (e : α → β) (he : Function.Injective e)
    (hstep : ∀ x xs f, AgreesOff (x :: xs) f e → step (x :: xs) f x (e x) = true)
    (xs : List α) (ys : List β) (f : α → β) (hn : xs.Nodup)
    (hy : ∀ x ∈ xs, e x ∈ ys) (hf : AgreesOff xs f e)
    (z : γ) (hz : z ∈ finish e) :
    z ∈ assignSearch step finish xs ys f := by
  induction xs generalizing ys f with
  | nil =>
    have hfe : f = e := funext fun x => hf x (by simp)
    subst f
    exact hz
  | cons x xs ih =>
    apply List.mem_flatMap.mpr
    refine ⟨e x,hy x (by simp),?_⟩
    rw [if_pos (hstep x xs f hf)]
    apply ih (ys.erase (e x)) (put f x (e x)) hn.of_cons
    · intro a ha
      have hax : a ≠ x := by
        intro h
        subst a
        exact (List.nodup_cons.mp hn).1 ha
      exact (List.mem_erase_of_ne (fun h => hax (he h))).mpr (hy a (by simp [ha]))
    · intro a ha
      by_cases hax : a = x
      · subst a
        simp
      · rw [put_ne _ _ _ hax]
        exact hf a (by simp [hax,ha])
end C13.Enumeration
