import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair17_15.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates17 : ∀ j : Fin 62, keys 17 = keys j → j ∈ ([15,17] : List (Fin 62)) := by decide +kernel

theorem unique17 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 17).center = hole)
    (hs : transport e (templates 17).star = (templates j).star) : (17 : Fin 62) = j := by
  have hj := candidates17 j (keys_invariant 17 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · have hm := Pair17_15.complete e he hc hs
    simp only [Pair17_15.maps,List.not_mem_nil] at hm
  · rfl
end C13.Enumeration.Canonical
