import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair02_12.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates02 : ∀ j : Fin 62, keys 2 = keys j → j ∈ ([2,12] : List (Fin 62)) := by decide +kernel

theorem unique02 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 2).center = hole)
    (hs : transport e (templates 2).star = (templates j).star) : (2 : Fin 62) = j := by
  have hj := candidates02 j (keys_invariant 2 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · rfl
  · have hm := Pair02_12.complete e he hc hs
    simp only [Pair02_12.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
