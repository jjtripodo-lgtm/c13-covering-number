import C13Enumeration.RawClass9.Table6
namespace C13.Enumeration.RawClass9.CoverageQ6Source05
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem centers_checked : ∀ c : Point, (link link05 c).card = 7 → c ∈ ([6,7,8,9,10,11] : List Point) := by decide +kernel

theorem complete (c : Point) (e : Equiv.Perm Point) (he : e hole = 6) (hc : e c = hole)
    (hs : transport e (link link05 c) = link link09 6) :
    ∃ p ∈ raw6.supported.domain.2, RepresentsPencil p (emitPencil link05 c 6 e) := by
  have hcard : (link link05 c).card = 7 := by
    calc
      _ = (transport e (link link05 c)).card := (transport_card e _).symm
      _ = (link link09 6).card := congrArg Finset.card hs
      _ = 7 := by decide +kernel
  have hm := centers_checked c hcard
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · have hn : ¬ HasPairCount (link link05 6) 4 := by decide +kernel
    have hp : HasPairCount (link link09 6) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mpr hp)).elim
  · have hn : ¬ HasPairCount (link link05 7) 4 := by decide +kernel
    have hp : HasPairCount (link link09 6) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mpr hp)).elim
  · have hn : ¬ HasPairCount (link link05 8) 4 := by decide +kernel
    have hp : HasPairCount (link link09 6) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mpr hp)).elim
  · have hn : ¬ HasPairCount (link link05 9) 4 := by decide +kernel
    have hp : HasPairCount (link link09 6) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mpr hp)).elim
  · have hn : ¬ HasPairCount (link link05 10) 4 := by decide +kernel
    have hp : HasPairCount (link link09 6) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mpr hp)).elim
  · have hn : ¬ HasPairCount (link link05 11) 4 := by decide +kernel
    have hp : HasPairCount (link link09 6) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mpr hp)).elim
end C13.Enumeration.RawClass9.CoverageQ6Source05
