import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair23_07.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates23 : ∀ j : Fin 62, keys 23 = keys j → j ∈ ([7,23] : List (Fin 62)) := by decide +kernel

theorem unique23 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 23).center = hole)
    (hs : transport e (templates 23).star = (templates j).star) : (23 : Fin 62) = j := by
  have hj := candidates23 j (keys_invariant 23 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · have hm := Pair23_07.complete e he hc hs
    simp only [Pair23_07.maps,List.not_mem_nil] at hm
  · rfl
end C13.Enumeration.Canonical
