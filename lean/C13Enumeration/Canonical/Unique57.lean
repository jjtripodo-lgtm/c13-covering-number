import C13Enumeration.Canonical.Profiles
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates57 : ∀ j : Fin 62, keys 57 = keys j → j ∈ ([57] : List (Fin 62)) := by decide +kernel

theorem unique57 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 57).center = hole)
    (hs : transport e (templates 57).star = (templates j).star) : (57 : Fin 62) = j := by
  have hj := candidates57 j (keys_invariant 57 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl
  rfl
end C13.Enumeration.Canonical
