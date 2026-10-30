import C13Enumeration.RawClass9.Table8
import C13Enumeration.RawClass9.BindQ8Source12Part0
namespace C13.Enumeration.RawClass9.CoverageQ8Source12
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem centers_checked : ∀ c : Point, (link link12 c).card = 7 → c ∈ ([2,3,6,7,10,11] : List Point) := by decide +kernel

theorem complete (c : Point) (e : Equiv.Perm Point) (he : e hole = 8) (hc : e c = hole)
    (hs : transport e (link link12 c) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link12 c 8 e) := by
  have hcard : (link link12 c).card = 7 := by
    calc
      _ = (transport e (link link12 c)).card := (transport_card e _).symm
      _ = (link link09 8).card := congrArg Finset.card hs
      _ = 7 := by decide +kernel
  have hm := centers_checked c hcard
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Source12Center02Q8.complete e he hc hs
  · exact Source12Center03Q8.complete e he hc hs
  · exact Source12Center06Q8.complete e he hc hs
  · exact Source12Center07Q8.complete e he hc hs
  · exact Source12Center10Q8.complete e he hc hs
  · exact Source12Center11Q8.complete e he hc hs
end C13.Enumeration.RawClass9.CoverageQ8Source12
