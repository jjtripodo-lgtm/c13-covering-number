import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair37_46.Complete
import C13Enumeration.Canonical.Pair37_48.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates37 : ∀ j : Fin 62, keys 37 = keys j → j ∈ ([37,46,48] : List (Fin 62)) := by decide +kernel

theorem unique37 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 37).center = hole)
    (hs : transport e (templates 37).star = (templates j).star) : (37 : Fin 62) = j := by
  have hj := candidates37 j (keys_invariant 37 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl
  · rfl
  · have hm := Pair37_46.complete e he hc hs
    simp only [Pair37_46.maps,List.not_mem_nil] at hm
  · have hm := Pair37_48.complete e he hc hs
    simp only [Pair37_48.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
