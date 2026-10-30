import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair39_49.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates39 : ∀ j : Fin 62, keys 39 = keys j → j ∈ ([39,49] : List (Fin 62)) := by decide +kernel

theorem unique39 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 39).center = hole)
    (hs : transport e (templates 39).star = (templates j).star) : (39 : Fin 62) = j := by
  have hj := candidates39 j (keys_invariant 39 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · rfl
  · have hm := Pair39_49.complete e he hc hs
    simp only [Pair39_49.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
