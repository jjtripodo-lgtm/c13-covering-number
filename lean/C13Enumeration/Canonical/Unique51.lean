import C13Enumeration.Canonical.Profiles
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates51 : ∀ j : Fin 62, keys 51 = keys j → j ∈ ([51] : List (Fin 62)) := by decide +kernel

theorem unique51 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 51).center = hole)
    (hs : transport e (templates 51).star = (templates j).star) : (51 : Fin 62) = j := by
  have hj := candidates51 j (keys_invariant 51 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl
  rfl
end C13.Enumeration.Canonical
