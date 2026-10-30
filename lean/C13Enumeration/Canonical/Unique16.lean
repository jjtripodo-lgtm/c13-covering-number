import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair16_25.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates16 : ∀ j : Fin 62, keys 16 = keys j → j ∈ ([16,25] : List (Fin 62)) := by decide +kernel

theorem unique16 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 16).center = hole)
    (hs : transport e (templates 16).star = (templates j).star) : (16 : Fin 62) = j := by
  have hj := candidates16 j (keys_invariant 16 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · rfl
  · have hm := Pair16_25.complete e he hc hs
    simp only [Pair16_25.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
