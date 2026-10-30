import C13Enumeration.Pilot.Data
namespace C13.Enumeration.Pilot.Source65
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem centers_checked : ∀ c : Point, (link link65 c).card = 9 → c ∈ ([8] : List Point) := by decide +kernel

theorem complete (c : Point) (e : Equiv.Perm Point) (he : e hole = 0) (hc : e c = hole)
    (hs : transport e (link link65 c) = link link01 0) : emitPencil link65 c 0 e = expected := by
  have hcard : (link link65 c).card = 9 := by
    calc
      _ = (transport e (link link65 c)).card := (transport_card e _).symm
      _ = (link link01 0).card := congrArg Finset.card hs
      _ = 9 := by decide +kernel
  have hm := centers_checked c hcard
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  exact (not_star_iso_of_signature (link link65 8) (link link01 0)
      (by decide +kernel) e hs).elim
end C13.Enumeration.Pilot.Source65
