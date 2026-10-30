import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair48_37.Complete
import C13Enumeration.Canonical.Pair48_46.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates48 : ∀ j : Fin 62, keys 48 = keys j → j ∈ ([37,46,48] : List (Fin 62)) := by decide +kernel

theorem unique48 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 48).center = hole)
    (hs : transport e (templates 48).star = (templates j).star) : (48 : Fin 62) = j := by
  have hj := candidates48 j (keys_invariant 48 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl
  · have hm := Pair48_37.complete e he hc hs
    simp only [Pair48_37.maps,List.not_mem_nil] at hm
  · have hm := Pair48_46.complete e he hc hs
    simp only [Pair48_46.maps,List.not_mem_nil] at hm
  · rfl
end C13.Enumeration.Canonical
