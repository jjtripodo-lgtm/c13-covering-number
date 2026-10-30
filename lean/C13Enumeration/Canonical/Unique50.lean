import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair50_41.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates50 : ∀ j : Fin 62, keys 50 = keys j → j ∈ ([41,50] : List (Fin 62)) := by decide +kernel

theorem unique50 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 50).center = hole)
    (hs : transport e (templates 50).star = (templates j).star) : (50 : Fin 62) = j := by
  have hj := candidates50 j (keys_invariant 50 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · have hm := Pair50_41.complete e he hc hs
    simp only [Pair50_41.maps,List.not_mem_nil] at hm
  · rfl
end C13.Enumeration.Canonical
