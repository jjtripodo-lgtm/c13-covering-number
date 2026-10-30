import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair20_00.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates20 : ∀ j : Fin 62, keys 20 = keys j → j ∈ ([0,20] : List (Fin 62)) := by decide +kernel

theorem unique20 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 20).center = hole)
    (hs : transport e (templates 20).star = (templates j).star) : (20 : Fin 62) = j := by
  have hj := candidates20 j (keys_invariant 20 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · have hm := Pair20_00.complete e he hc hs
    simp only [Pair20_00.maps,List.not_mem_nil] at hm
  · rfl
end C13.Enumeration.Canonical
