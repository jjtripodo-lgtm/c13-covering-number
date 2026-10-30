import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair12_02.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates12 : ∀ j : Fin 62, keys 12 = keys j → j ∈ ([2,12] : List (Fin 62)) := by decide +kernel

theorem unique12 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 12).center = hole)
    (hs : transport e (templates 12).star = (templates j).star) : (12 : Fin 62) = j := by
  have hj := candidates12 j (keys_invariant 12 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · have hm := Pair12_02.complete e he hc hs
    simp only [Pair12_02.maps,List.not_mem_nil] at hm
  · rfl
end C13.Enumeration.Canonical
