import C13Enumeration.Pilot.Data
import C13Enumeration.Pilot.Source50Center04
import C13Enumeration.Pilot.Source50Center05
namespace C13.Enumeration.Pilot.Source50
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem centers_checked : ∀ c : Point, (link link50 c).card = 9 → c ∈ ([4,5] : List Point) := by decide +kernel

theorem complete (c : Point) (e : Equiv.Perm Point) (he : e hole = 0) (hc : e c = hole)
    (hs : transport e (link link50 c) = link link01 0) : emitPencil link50 c 0 e = expected := by
  have hcard : (link link50 c).card = 9 := by
    calc
      _ = (transport e (link link50 c)).card := (transport_card e _).symm
      _ = (link link01 0).card := congrArg Finset.card hs
      _ = 9 := by decide +kernel
  have hm := centers_checked c hcard
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact Source50Center04.complete e he hc hs
  · exact Source50Center05.complete e he hc hs
end C13.Enumeration.Pilot.Source50
