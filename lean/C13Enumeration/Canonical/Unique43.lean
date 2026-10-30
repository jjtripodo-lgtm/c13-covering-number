import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair43_30.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates43 : ∀ j : Fin 62, keys 43 = keys j → j ∈ ([30,43] : List (Fin 62)) := by decide +kernel

theorem unique43 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 43).center = hole)
    (hs : transport e (templates 43).star = (templates j).star) : (43 : Fin 62) = j := by
  have hj := candidates43 j (keys_invariant 43 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · have hm := Pair43_30.complete e he hc hs
    simp only [Pair43_30.maps,List.not_mem_nil] at hm
  · rfl
end C13.Enumeration.Canonical
