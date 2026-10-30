import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair24_13.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates24 : ∀ j : Fin 62, keys 24 = keys j → j ∈ ([13,24] : List (Fin 62)) := by decide +kernel

theorem unique24 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 24).center = hole)
    (hs : transport e (templates 24).star = (templates j).star) : (24 : Fin 62) = j := by
  have hj := candidates24 j (keys_invariant 24 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · have hm := Pair24_13.complete e he hc hs
    simp only [Pair24_13.maps,List.not_mem_nil] at hm
  · rfl
end C13.Enumeration.Canonical
