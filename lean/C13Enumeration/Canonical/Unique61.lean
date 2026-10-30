import C13Enumeration.Canonical.Profiles
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates61 : ∀ j : Fin 62, keys 61 = keys j → j ∈ ([61] : List (Fin 62)) := by decide +kernel

theorem unique61 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 61).center = hole)
    (hs : transport e (templates 61).star = (templates j).star) : (61 : Fin 62) = j := by
  have hj := candidates61 j (keys_invariant 61 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl
  rfl
end C13.Enumeration.Canonical
