import C13Enumeration.DegreeEightPilot.Data
import C13Enumeration.DegreeEightPilot.Source57Center01
import C13Enumeration.DegreeEightPilot.Source57Center08
namespace C13.Enumeration.DegreeEightPilot.Source57
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem candidates_checked : ∀ c : Point, (link link57 c).card = 8 →
    degreeSignature (link link57 c) = degreeSignature (link link01 4) →
    c ∈ ([1,8] : List Point) := by decide +kernel

theorem complete (c : Point) (e : Equiv.Perm Point) (he : e hole = 4) (hc : e c = hole)
    (hs : transport e (link link57 c) = link link01 4) :
    ∃ p ∈ codedDomain.supported.domain.2, RepresentsPencil p (emitPencil link57 c 4 e) := by
  have hcard : (link link57 c).card = 8 := by
    calc
      _ = (transport e (link link57 c)).card := (transport_card e _).symm
      _ = (link link01 4).card := congrArg Finset.card hs
      _ = 8 := by decide +kernel
  have hm := candidates_checked c hcard (degreeSignature_transport _ _ e hs)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl
  · exact Source57Center01.complete e he hc hs
  · exact Source57Center08.complete e he hc hs
end C13.Enumeration.DegreeEightPilot.Source57
