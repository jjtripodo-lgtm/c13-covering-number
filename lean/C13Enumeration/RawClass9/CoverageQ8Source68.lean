import C13Enumeration.RawClass9.Table8
namespace C13.Enumeration.RawClass9.CoverageQ8Source68
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem centers_checked : ∀ c : Point, (link figure6 c).card = 7 → c ∈ ([0,1,2,3,6,7,8,9,10,11] : List Point) := by decide +kernel

theorem complete (c : Point) (e : Equiv.Perm Point) (he : e hole = 8) (hc : e c = hole)
    (hs : transport e (link figure6 c) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil figure6 c 8 e) := by
  have hcard : (link figure6 c).card = 7 := by
    calc
      _ = (transport e (link figure6 c)).card := (transport_card e _).symm
      _ = (link link09 8).card := congrArg Finset.card hs
      _ = 7 := by decide +kernel
  have hm := centers_checked c hcard
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hp : HasPairCount (link figure6 0) 4 := by decide +kernel
    have hn : ¬ HasPairCount (link link09 8) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mp hp)).elim
  · have hp : HasPairCount (link figure6 1) 4 := by decide +kernel
    have hn : ¬ HasPairCount (link link09 8) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mp hp)).elim
  · have hp : HasPairCount (link figure6 2) 4 := by decide +kernel
    have hn : ¬ HasPairCount (link link09 8) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mp hp)).elim
  · have hp : HasPairCount (link figure6 3) 4 := by decide +kernel
    have hn : ¬ HasPairCount (link link09 8) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mp hp)).elim
  · have hp : HasPairCount (link figure6 6) 4 := by decide +kernel
    have hn : ¬ HasPairCount (link link09 8) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mp hp)).elim
  · have hp : HasPairCount (link figure6 7) 4 := by decide +kernel
    have hn : ¬ HasPairCount (link link09 8) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mp hp)).elim
  · have hp : HasPairCount (link figure6 8) 4 := by decide +kernel
    have hn : ¬ HasPairCount (link link09 8) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mp hp)).elim
  · have hp : HasPairCount (link figure6 9) 4 := by decide +kernel
    have hn : ¬ HasPairCount (link link09 8) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mp hp)).elim
  · have hp : HasPairCount (link figure6 10) 4 := by decide +kernel
    have hn : ¬ HasPairCount (link link09 8) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mp hp)).elim
  · have hp : HasPairCount (link figure6 11) 4 := by decide +kernel
    have hn : ¬ HasPairCount (link link09 8) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mp hp)).elim
end C13.Enumeration.RawClass9.CoverageQ8Source68
