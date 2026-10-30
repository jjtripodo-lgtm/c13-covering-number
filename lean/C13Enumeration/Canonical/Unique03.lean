import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair03_11.Complete
import C13Enumeration.Canonical.Pair03_21.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates03 : ∀ j : Fin 62, keys 3 = keys j → j ∈ ([3,11,21] : List (Fin 62)) := by decide +kernel

theorem unique03 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 3).center = hole)
    (hs : transport e (templates 3).star = (templates j).star) : (3 : Fin 62) = j := by
  have hj := candidates03 j (keys_invariant 3 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl
  · rfl
  · have hm := Pair03_11.complete e he hc hs
    simp only [Pair03_11.maps,List.not_mem_nil] at hm
  · have hm := Pair03_21.complete e he hc hs
    simp only [Pair03_21.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
