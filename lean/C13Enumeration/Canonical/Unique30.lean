import C13Enumeration.Canonical.Profiles
import C13Enumeration.Canonical.Pair30_43.Complete
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates30 : ∀ j : Fin 62, keys 30 = keys j → j ∈ ([30,43] : List (Fin 62)) := by decide +kernel

theorem unique30 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 30).center = hole)
    (hs : transport e (templates 30).star = (templates j).star) : (30 : Fin 62) = j := by
  have hj := candidates30 j (keys_invariant 30 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl
  · rfl
  · have hm := Pair30_43.complete e he hc hs
    simp only [Pair30_43.maps,List.not_mem_nil] at hm
end C13.Enumeration.Canonical
