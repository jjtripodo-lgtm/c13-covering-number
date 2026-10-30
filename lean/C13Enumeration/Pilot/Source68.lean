import C13Enumeration.Pilot.Data
namespace C13.Enumeration.Pilot.Source68
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem centers_checked : ∀ c : Point, (link figure6 c).card = 9 → c ∈ ([] : List Point) := by decide +kernel

theorem complete (c : Point) (e : Equiv.Perm Point) (he : e hole = 0) (hc : e c = hole)
    (hs : transport e (link figure6 c) = link link01 0) : emitPencil figure6 c 0 e = expected := by
  have hcard : (link figure6 c).card = 9 := by
    calc
      _ = (transport e (link figure6 c)).card := (transport_card e _).symm
      _ = (link link01 0).card := congrArg Finset.card hs
      _ = 9 := by decide +kernel
  have hm := centers_checked c hcard
  simp at hm
end C13.Enumeration.Pilot.Source68
