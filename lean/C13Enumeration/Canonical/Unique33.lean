import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair33_47.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates33 : ∀ j : Fin 62, keys 33 = keys j → j ∈ ([33,47] : List (Fin 62)) := by decide +kernel

theorem unique33 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 33).center = hole)
    (hs : transport e (templates 33).star = (templates j).star) : (33 : Fin 62) = j := by
  have hj := candidates33 j (keys_invariant 33 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · rfl
  · have hm := Pair33_47.complete e he hc hs
    simp only [Pair33_47.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
