import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair04_09.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates04 : ∀ j : Fin 62, keys 4 = keys j → j ∈ ([4,9] : List (Fin 62)) := by decide +kernel

theorem unique04 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 4).center = hole)
    (hs : transport e (templates 4).star = (templates j).star) : (4 : Fin 62) = j := by
  have hj := candidates04 j (keys_invariant 4 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · rfl
  · have hm := Pair04_09.complete e he hc hs
    simp only [Pair04_09.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
