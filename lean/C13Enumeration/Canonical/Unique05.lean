import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair05_22.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates05 : ∀ j : Fin 62, keys 5 = keys j → j ∈ ([5,22] : List (Fin 62)) := by decide +kernel

theorem unique05 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 5).center = hole)
    (hs : transport e (templates 5).star = (templates j).star) : (5 : Fin 62) = j := by
  have hj := candidates05 j (keys_invariant 5 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · rfl
  · have hm := Pair05_22.complete e he hc hs
    simp only [Pair05_22.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
