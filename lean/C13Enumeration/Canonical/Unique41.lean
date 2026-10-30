import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair41_50.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates41 : ∀ j : Fin 62, keys 41 = keys j → j ∈ ([41,50] : List (Fin 62)) := by decide +kernel

theorem unique41 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 41).center = hole)
    (hs : transport e (templates 41).star = (templates j).star) : (41 : Fin 62) = j := by
  have hj := candidates41 j (keys_invariant 41 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · rfl
  · have hm := Pair41_50.complete e he hc hs
    simp only [Pair41_50.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
