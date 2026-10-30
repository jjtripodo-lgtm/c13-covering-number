import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair07_23.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates07 : ∀ j : Fin 62, keys 7 = keys j → j ∈ ([7,23] : List (Fin 62)) := by decide +kernel

theorem unique07 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 7).center = hole)
    (hs : transport e (templates 7).star = (templates j).star) : (7 : Fin 62) = j := by
  have hj := candidates07 j (keys_invariant 7 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · rfl
  · have hm := Pair07_23.complete e he hc hs
    simp only [Pair07_23.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
