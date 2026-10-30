import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair49_39.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates49 : ∀ j : Fin 62, keys 49 = keys j → j ∈ ([39,49] : List (Fin 62)) := by decide +kernel

theorem unique49 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 49).center = hole)
    (hs : transport e (templates 49).star = (templates j).star) : (49 : Fin 62) = j := by
  have hj := candidates49 j (keys_invariant 49 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · have hm := Pair49_39.complete e he hc hs
    simp only [Pair49_39.maps,List.not_mem_nil] at hm
  · rfl
end C13.Enumeration.Canonical
