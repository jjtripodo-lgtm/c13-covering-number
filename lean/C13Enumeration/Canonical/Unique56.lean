import C13Enumeration.Canonical.Profiles
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates56 : ∀ j : Fin 62, keys 56 = keys j → j ∈ ([56] : List (Fin 62)) := by decide +kernel

theorem unique56 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 56).center = hole)
    (hs : transport e (templates 56).star = (templates j).star) : (56 : Fin 62) = j := by
  have hj := candidates56 j (keys_invariant 56 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl
  rfl
end C13.Enumeration.Canonical
