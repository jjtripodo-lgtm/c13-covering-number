import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair36_32.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates36 : ∀ j : Fin 62, keys 36 = keys j → j ∈ ([32,36] : List (Fin 62)) := by decide +kernel

theorem unique36 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 36).center = hole)
    (hs : transport e (templates 36).star = (templates j).star) : (36 : Fin 62) = j := by
  have hj := candidates36 j (keys_invariant 36 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · have hm := Pair36_32.complete e he hc hs
    simp only [Pair36_32.maps,List.not_mem_nil] at hm
  · rfl
end C13.Enumeration.Canonical
