import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair09_04.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates09 : ∀ j : Fin 62, keys 9 = keys j → j ∈ ([4,9] : List (Fin 62)) := by decide +kernel

theorem unique09 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 9).center = hole)
    (hs : transport e (templates 9).star = (templates j).star) : (9 : Fin 62) = j := by
  have hj := candidates09 j (keys_invariant 9 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · have hm := Pair09_04.complete e he hc hs
    simp only [Pair09_04.maps,List.not_mem_nil] at hm
  · rfl
end C13.Enumeration.Canonical
