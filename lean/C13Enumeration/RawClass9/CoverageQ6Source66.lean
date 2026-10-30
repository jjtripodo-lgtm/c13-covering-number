import C13Enumeration.RawClass9.Table6
import C13Enumeration.RawClass9.BindQ6Source66Part0
namespace C13.Enumeration.RawClass9.CoverageQ6Source66
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem centers_checked : ∀ c : Point, (link link66 c).card = 7 → c ∈ ([0,3,6,7,9,11] : List Point) := by decide +kernel

theorem complete (c : Point) (e : Equiv.Perm Point) (he : e hole = 6) (hc : e c = hole)
    (hs : transport e (link link66 c) = link link09 6) :
    ∃ p ∈ raw6.supported.domain.2, RepresentsPencil p (emitPencil link66 c 6 e) := by
  have hcard : (link link66 c).card = 7 := by
    calc
      _ = (transport e (link link66 c)).card := (transport_card e _).symm
      _ = (link link09 6).card := congrArg Finset.card hs
      _ = 7 := by decide +kernel
  have hm := centers_checked c hcard
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Source66Center00Q6.complete e he hc hs
  · have hn : ¬ HasPairCount (link link66 3) 4 := by decide +kernel
    have hp : HasPairCount (link link09 6) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mpr hp)).elim
  · have hn : ¬ HasPairCount (link link66 6) 4 := by decide +kernel
    have hp : HasPairCount (link link09 6) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mpr hp)).elim
  · exact Source66Center07Q6.complete e he hc hs
  · have hn : ¬ HasPairCount (link link66 9) 4 := by decide +kernel
    have hp : HasPairCount (link link09 6) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mpr hp)).elim
  · exact Source66Center11Q6.complete e he hc hs
end C13.Enumeration.RawClass9.CoverageQ6Source66
