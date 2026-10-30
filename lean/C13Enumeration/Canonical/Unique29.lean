import C13Enumeration.Canonical.Profiles
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem candidates29 : ∀ j : Fin 62, keys 29 = keys j → j ∈ ([29] : List (Fin 62)) := by decide +kernel

theorem unique29 (j : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates j).center) (hc : e (templates 29).center = hole)
    (hs : transport e (templates 29).star = (templates j).star) : (29 : Fin 62) = j := by
  have hj := candidates29 j (keys_invariant 29 j e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl
  rfl
end C13.Enumeration.Canonical
