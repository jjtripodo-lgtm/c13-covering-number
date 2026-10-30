import C13Enumeration.Canonical.Normalizers.Source01
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source01
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem complete00 : SourceComplete domains Normalizers.Source01.record00 := by
  intro _ e he hc hs
  change ∃ p ∈ Pilot.codedDomain.supported.domain.2, RepresentsPencil p (emitPencil link01 0 0 e)
  refine ⟨decodePencil (Pilot.codedDomain.pencil Pilot.codedRow),
    decoded_row_mem _ _ (by decide +kernel),?_⟩
  rw [Pilot.Source01Center00.complete e he hc hs]
  exact Pilot.decoded_pencil_checked

theorem complete01 : SourceComplete domains Normalizers.Source01.record01 := by
  intro _ e he hc hs
  change ∃ p ∈ Pilot.codedDomain.supported.domain.2, RepresentsPencil p (emitPencil link01 1 0 e)
  refine ⟨decodePencil (Pilot.codedDomain.pencil Pilot.codedRow),
    decoded_row_mem _ _ (by decide +kernel),?_⟩
  rw [Pilot.Source01Center01.complete e he hc hs]
  exact Pilot.decoded_pencil_checked

theorem complete02 : SourceComplete domains Normalizers.Source01.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source01Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source01.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source01Center03Q8.complete e he hc hs

theorem complete04 : SourceComplete domains Normalizers.Source01.record04 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source01Center04.complete e he hc hs

theorem complete05 : SourceComplete domains Normalizers.Source01.record05 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source01Center05.complete e he hc hs

theorem complete06 : SourceComplete domains Normalizers.Source01.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source01Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source01.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source01Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source01.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source01Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source01.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source01Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source01.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source01Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source01.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source01Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source01.entries, SourceComplete domains r := by
  simp only [Normalizers.Source01.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source01
