import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair00_20.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates00 : ∀ j : Fin 62, keys 0 = keys j → j ∈ ([0,20] : List (Fin 62)) := by decide +kernel

theorem unique00 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 0).center = hole)
    (hs : transport e (templates 0).star = (templates j).star) : (0 : Fin 62) = j := by
  have hj := candidates00 j (keys_invariant 0 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · rfl
  · have hm := Pair00_20.complete e he hc hs
    simp only [Pair00_20.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
