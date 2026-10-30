import C13Enumeration.RawClass9.Table8
import C13Enumeration.RawClass9.BindQ8Source55Part0
namespace C13.Enumeration.RawClass9.CoverageQ8Source55
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem centers_checked : ∀ c : Point, (link link55 c).card = 7 → c ∈ ([2,3,5,7,9,10,11] : List Point) := by decide +kernel

theorem complete (c : Point) (e : Equiv.Perm Point) (he : e hole = 8) (hc : e c = hole)
    (hs : transport e (link link55 c) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link55 c 8 e) := by
  have hcard : (link link55 c).card = 7 := by
    calc
      _ = (transport e (link link55 c)).card := (transport_card e _).symm
      _ = (link link09 8).card := congrArg Finset.card hs
      _ = 7 := by decide +kernel
  have hm := centers_checked c hcard
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Source55Center02Q8.complete e he hc hs
  · exact Source55Center03Q8.complete e he hc hs
  · exact Source55Center05Q8.complete e he hc hs
  · exact Source55Center07Q8.complete e he hc hs
  · exact Source55Center09Q8.complete e he hc hs
  · exact Source55Center10Q8.complete e he hc hs
  · have hp : HasPairCount (link link55 11) 4 := by decide +kernel
    have hn : ¬ HasPairCount (link link09 8) 4 := by decide +kernel
    exact (hn ((hasPairCount_transport _ _ e hs 4).mp hp)).elim
end C13.Enumeration.RawClass9.CoverageQ8Source55
