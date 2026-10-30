import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair11_03.Complete
import C13Enumeration.Canonical.Pair11_21.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates11 : ∀ j : Fin 62, keys 11 = keys j → j ∈ ([3,11,21] : List (Fin 62)) := by decide +kernel

theorem unique11 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 11).center = hole)
    (hs : transport e (templates 11).star = (templates j).star) : (11 : Fin 62) = j := by
  have hj := candidates11 j (keys_invariant 11 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl
  · have hm := Pair11_03.complete e he hc hs
    simp only [Pair11_03.maps,List.not_mem_nil] at hm
  · rfl
  · have hm := Pair11_21.complete e he hc hs
    simp only [Pair11_21.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
