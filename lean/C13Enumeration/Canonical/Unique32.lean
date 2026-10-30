import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair32_36.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates32 : ∀ j : Fin 62, keys 32 = keys j → j ∈ ([32,36] : List (Fin 62)) := by decide +kernel

theorem unique32 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 32).center = hole)
    (hs : transport e (templates 32).star = (templates j).star) : (32 : Fin 62) = j := by
  have hj := candidates32 j (keys_invariant 32 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · rfl
  · have hm := Pair32_36.complete e he hc hs
    simp only [Pair32_36.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
