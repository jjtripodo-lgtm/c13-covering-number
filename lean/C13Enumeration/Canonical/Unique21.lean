import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair21_03.Complete
import C13Enumeration.Canonical.Pair21_11.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates21 : ∀ j : Fin 62, keys 21 = keys j → j ∈ ([3,11,21] : List (Fin 62)) := by decide +kernel

theorem unique21 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 21).center = hole)
    (hs : transport e (templates 21).star = (templates j).star) : (21 : Fin 62) = j := by
  have hj := candidates21 j (keys_invariant 21 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl
  · have hm := Pair21_03.complete e he hc hs
    simp only [Pair21_03.maps,List.not_mem_nil] at hm
  · have hm := Pair21_11.complete e he hc hs
    simp only [Pair21_11.maps,List.not_mem_nil] at hm
  · rfl
end C13.Enumeration.Canonical
