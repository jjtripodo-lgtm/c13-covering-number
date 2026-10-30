import C13Enumeration.RawClass9.Table6
import C13Enumeration.RawClass9.BindQ6Source68Part0
import C13Enumeration.RawClass9.BindQ6Source68Part1
import C13Enumeration.RawClass9.BindQ6Source68Part2
namespace C13.Enumeration.RawClass9.CoverageQ6Source68
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem centers_checked : ∀ c : Point, (link figure6 c).card = 7 → c ∈ ([0,1,2,3,6,7,8,9,10,11] : List Point) := by decide +kernel

theorem complete (c : Point) (e : Equiv.Perm Point) (he : e hole = 6) (hc : e c = hole)
    (hs : transport e (link figure6 c) = link link09 6) :
    ∃ p ∈ raw6.supported.domain.2, RepresentsPencil p (emitPencil figure6 c 6 e) := by
  have hcard : (link figure6 c).card = 7 := by
    calc
      _ = (transport e (link figure6 c)).card := (transport_card e _).symm
      _ = (link link09 6).card := congrArg Finset.card hs
      _ = 7 := by decide +kernel
  have hm := centers_checked c hcard
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Source68Center00Q6.complete e he hc hs
  · exact Source68Center01Q6.complete e he hc hs
  · exact Source68Center02Q6.complete e he hc hs
  · exact Source68Center03Q6.complete e he hc hs
  · exact Source68Center06Q6.complete e he hc hs
  · exact Source68Center07Q6.complete e he hc hs
  · exact Source68Center08Q6.complete e he hc hs
  · exact Source68Center09Q6.complete e he hc hs
  · exact Source68Center10Q6.complete e he hc hs
  · exact Source68Center11Q6.complete e he hc hs
end C13.Enumeration.RawClass9.CoverageQ6Source68
