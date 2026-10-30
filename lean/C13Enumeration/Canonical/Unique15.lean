import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair15_17.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates15 : ∀ j : Fin 62, keys 15 = keys j → j ∈ ([15,17] : List (Fin 62)) := by decide +kernel

theorem unique15 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 15).center = hole)
    (hs : transport e (templates 15).star = (templates j).star) : (15 : Fin 62) = j := by
  have hj := candidates15 j (keys_invariant 15 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · rfl
  · have hm := Pair15_17.complete e he hc hs
    simp only [Pair15_17.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
