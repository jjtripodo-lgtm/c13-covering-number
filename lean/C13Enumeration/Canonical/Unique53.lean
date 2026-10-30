import C13Enumeration.Canonical.Profiles
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates53 : ∀ j : Fin 62, keys 53 = keys j → j ∈ ([53] : List (Fin 62)) := by decide +kernel

theorem unique53 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 53).center = hole)
    (hs : transport e (templates 53).star = (templates j).star) : (53 : Fin 62) = j := by
  have hj := candidates53 j (keys_invariant 53 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl
  rfl
end C13.Enumeration.Canonical
