import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair25_16.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates25 : ∀ j : Fin 62, keys 25 = keys j → j ∈ ([16,25] : List (Fin 62)) := by decide +kernel

theorem unique25 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 25).center = hole)
    (hs : transport e (templates 25).star = (templates j).star) : (25 : Fin 62) = j := by
  have hj := candidates25 j (keys_invariant 25 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · have hm := Pair25_16.complete e he hc hs
    simp only [Pair25_16.maps,List.not_mem_nil] at hm
  · rfl
end C13.Enumeration.Canonical
