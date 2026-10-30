import C13Arc.Selection

/-! A cheaper necessary support test. A chosen shared block must occur somewhere
in the other point's domain. Overapproximations are sound; completeness is not
inferred from successful checking. -/
namespace C13.Checker.RawSupport
open Arc

structure SupportedDomain where
  domain : Domain
  possible : Finset Block
  covers : ∀ p ∈ domain.2, ∀ b ∈ p, b ∈ possible

def domains (ds : List SupportedDomain) : List Domain := ds.map SupportedDomain.domain

def supportKeep (ds : List SupportedDomain) (q : Nat) (p : Pencil) : Bool :=
  ds.all fun d => if q = d.domain.1 then true else
    p.all fun b => decide (d.domain.1 ∈ b → b ∈ d.possible)

def supportStep (ds : List SupportedDomain) : List Domain :=
  ds.map fun d => (d.domain.1, d.domain.2.filter (supportKeep ds d.domain.1))

theorem supportKeep_of_witness {budget : Nat} {ds : List SupportedDomain} {pick : Choice}
    (h : JointWitness budget (domains ds) pick) {d : SupportedDomain} (hd : d ∈ ds) :
    supportKeep ds d.domain.1 (pick d.domain.1) = true := by
  apply List.all_eq_true.mpr
  intro e he
  split
  · rfl
  · apply List.all_eq_true.mpr
    intro b hb
    apply decide_eq_true
    intro hep
    have hde := h.2.1 d.domain (List.mem_map.mpr ⟨d,hd,rfl⟩)
      e.domain (List.mem_map.mpr ⟨e,he,rfl⟩)
    have hepick := ((compatible_iff _ _ _ _).mp hde b).mp ⟨hb,hep⟩
    exact e.covers (pick e.domain.1) (h.1 e.domain (List.mem_map.mpr ⟨e,he,rfl⟩)) b hepick.1

theorem selectedOf_supportStep (ds : List SupportedDomain) (pick : Choice) :
    selectedOf (supportStep ds) pick = selectedOf (domains ds) pick := by
  simp [selectedOf, supportStep, domains, List.map_map, Function.comp_def]

theorem witness_survives_support {budget : Nat} {ds : List SupportedDomain} {pick : Choice}
    (h : JointWitness budget (domains ds) pick) :
    JointWitness budget (supportStep ds) pick := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp he
    exact List.mem_filter.mpr ⟨h.1 d.domain (List.mem_map.mpr ⟨d,hd,rfl⟩),
      supportKeep_of_witness h hd⟩
  · intro d hd e he
    obtain ⟨d₀,hd₀,rfl⟩ := List.mem_map.mp hd
    obtain ⟨e₀,he₀,rfl⟩ := List.mem_map.mp he
    exact h.2.1 d₀.domain (List.mem_map.mpr ⟨d₀,hd₀,rfl⟩)
      e₀.domain (List.mem_map.mpr ⟨e₀,he₀,rfl⟩)
  · simpa only [selectedOf_supportStep] using h.2.2

theorem hasJoin_survives_support {budget : Nat} {ds : List SupportedDomain}
    (labels : ((domains ds).map Prod.fst).Nodup) (h : HasJoin budget (domains ds) []) :
    HasJoin budget (supportStep ds) [] := by
  obtain ⟨pick,hpick⟩ := exists_jointWitness_of_hasJoin labels h
  exact hasJoin_of_jointWitness (witness_survives_support hpick)

end C13.Checker.RawSupport
