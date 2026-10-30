import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair22_05.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates22 : ∀ j : Fin 62, keys 22 = keys j → j ∈ ([5,22] : List (Fin 62)) := by decide +kernel

theorem unique22 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 22).center = hole)
    (hs : transport e (templates 22).star = (templates j).star) : (22 : Fin 62) = j := by
  have hj := candidates22 j (keys_invariant 22 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · have hm := Pair22_05.complete e he hc hs
    simp only [Pair22_05.maps,List.not_mem_nil] at hm
  · rfl
end C13.Enumeration.Canonical
