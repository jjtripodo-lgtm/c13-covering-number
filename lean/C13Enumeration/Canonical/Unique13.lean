import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair13_24.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates13 : ∀ j : Fin 62, keys 13 = keys j → j ∈ ([13,24] : List (Fin 62)) := by decide +kernel

theorem unique13 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 13).center = hole)
    (hs : transport e (templates 13).star = (templates j).star) : (13 : Fin 62) = j := by
  have hj := candidates13 j (keys_invariant 13 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · rfl
  · have hm := Pair13_24.complete e he hc hs
    simp only [Pair13_24.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
