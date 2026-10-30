import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair47_33.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates47 : ∀ j : Fin 62, keys 47 = keys j → j ∈ ([33,47] : List (Fin 62)) := by decide +kernel

theorem unique47 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 47).center = hole)
    (hs : transport e (templates 47).star = (templates j).star) : (47 : Fin 62) = j := by
  have hj := candidates47 j (keys_invariant 47 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · have hm := Pair47_33.complete e he hc hs
    simp only [Pair47_33.maps,List.not_mem_nil] at hm
  · rfl
end C13.Enumeration.Canonical
