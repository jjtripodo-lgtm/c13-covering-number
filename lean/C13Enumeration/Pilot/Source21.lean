import C13Enumeration.Pilot.Data
import C13Enumeration.Pilot.Source21Center00
namespace C13.Enumeration.Pilot.Source21
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem centers_checked : ∀ c : Point, (link link21 c).card = 9 → c ∈ ([0] : List Point) := by decide +kernel

theorem complete (c : Point) (e : Equiv.Perm Point) (he : e hole = 0) (hc : e c = hole)
    (hs : transport e (link link21 c) = link link01 0) : emitPencil link21 c 0 e = expected := by
  have hcard : (link link21 c).card = 9 := by
    calc
      _ = (transport e (link link21 c)).card := (transport_card e _).symm
      _ = (link link01 0).card := congrArg Finset.card hs
      _ = 9 := by decide +kernel
  have hm := centers_checked c hcard
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  exact Source21Center00.complete e he hc hs
end C13.Enumeration.Pilot.Source21
