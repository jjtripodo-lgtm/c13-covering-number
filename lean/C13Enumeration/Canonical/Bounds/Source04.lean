import C13Enumeration.Canonical.Normalizers.Source04
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source04
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 7).length → (table 7).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 7).length) : Bool :=
  decide (((domains 7).pencil ((table 7).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes04 0 0 (fun x => (maps 7).get i (Normalizers.Source04.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 7).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 7).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 7).length = (((List.finRange (maps 7).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 7).length,
    ((domains 7).pencil ((table 7).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes04 0 0 (fun x => (maps 7).get i (Normalizers.Source04.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source04.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 7) link04 (templates 7).family hole 0 0
    Normalizers.Source04.normalizer00 Normalizers.Source04.record00.hole_fixed Normalizers.Source04.record00.center_image Normalizers.Source04.record00.star_image
    (maps 7) (maps_complete 7) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 7) (table 7)
    RawClass9.CatalogCodes.codes04 link04 RawClass9.CatalogCodes.checked04
    0 0 Normalizers.Source04.normalizer00 (maps 7) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source04.record01 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source04Center01.complete e he hc hs

theorem complete02 : SourceComplete domains Normalizers.Source04.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source04Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source04.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source04Center03Q8.complete e he hc hs

theorem complete04 : SourceComplete domains Normalizers.Source04.record04 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source04Center04.complete e he hc hs

theorem complete05 : SourceComplete domains Normalizers.Source04.record05 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source04Center05.complete e he hc hs

def pick06 : Fin (maps 8).length → (table 8).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck06 (i : Fin (maps 8).length) : Bool :=
  decide (((domains 8).pencil ((table 8).row (pick06 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes04 6 6 (fun x => (maps 8).get i (Normalizers.Source04.normalizer06 x))).toFinset)

theorem chunk06_0 : ((((List.finRange (maps 8).length).drop 0).take 16).all rowCheck06) = true := by decide +kernel
theorem all06 : ((List.finRange (maps 8).length).all rowCheck06) = true := by
  have hsplit : List.finRange (maps 8).length = (((List.finRange (maps 8).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk06_0
theorem rows06 : ∀ i : Fin (maps 8).length,
    ((domains 8).pencil ((table 8).row (pick06 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes04 6 6 (fun x => (maps 8).get i (Normalizers.Source04.normalizer06 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all06) i (by simp))

theorem complete06 : SourceComplete domains Normalizers.Source04.record06 := by
  intro _ e he hc hs
  apply source_center_represented (domains 8) link04 (templates 8).family hole 6 6
    Normalizers.Source04.normalizer06 Normalizers.Source04.record06.hole_fixed Normalizers.Source04.record06.center_image Normalizers.Source04.record06.star_image
    (maps 8) (maps_complete 8) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 8) (table 8)
    RawClass9.CatalogCodes.codes04 link04 RawClass9.CatalogCodes.checked04
    6 6 Normalizers.Source04.normalizer06 (maps 8) pick06 rows06

theorem complete07 : SourceComplete domains Normalizers.Source04.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source04Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source04.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source04Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source04.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source04Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source04.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source04Center10Q6.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source04.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source04Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source04.entries, SourceComplete domains r := by
  simp only [Normalizers.Source04.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source04
