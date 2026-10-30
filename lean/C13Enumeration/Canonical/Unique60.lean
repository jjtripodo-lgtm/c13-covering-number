import C13Enumeration.Canonical.Profiles
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates60 : ∀ j : Fin 62, keys 60 = keys j → j ∈ ([60] : List (Fin 62)) := by decide +kernel

theorem unique60 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 60).center = hole)
    (hs : transport e (templates 60).star = (templates j).star) : (60 : Fin 62) = j := by
  have hj := candidates60 j (keys_invariant 60 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl
  rfl
end C13.Enumeration.Canonical
