import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair46_37.Complete
import C13Enumeration.Canonical.Pair46_48.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates46 : ∀ j : Fin 62, keys 46 = keys j → j ∈ ([37,46,48] : List (Fin 62)) := by decide +kernel

theorem unique46 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 46).center = hole)
    (hs : transport e (templates 46).star = (templates j).star) : (46 : Fin 62) = j := by
  have hj := candidates46 j (keys_invariant 46 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl
  · have hm := Pair46_37.complete e he hc hs
    simp only [Pair46_37.maps,List.not_mem_nil] at hm
  · rfl
  · have hm := Pair46_48.complete e he hc hs
    simp only [Pair46_48.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
