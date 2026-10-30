import C13Enumeration.Canonical.Normalizers.Source03
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source03
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 5).length → (table 5).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 5).length) : Bool :=
  decide (((domains 5).pencil ((table 5).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes03 0 0 (fun x => (maps 5).get i (Normalizers.Source03.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 5).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 5).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 5).length = (((List.finRange (maps 5).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 5).length,
    ((domains 5).pencil ((table 5).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes03 0 0 (fun x => (maps 5).get i (Normalizers.Source03.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source03.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 5) link03 (templates 5).family hole 0 0
    Normalizers.Source03.normalizer00 Normalizers.Source03.record00.hole_fixed Normalizers.Source03.record00.center_image Normalizers.Source03.record00.star_image
    (maps 5) (maps_complete 5) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 5) (table 5)
    RawClass9.CatalogCodes.codes03 link03 RawClass9.CatalogCodes.checked03
    0 0 Normalizers.Source03.normalizer00 (maps 5) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source03.record01 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source03Center01.complete e he hc hs

theorem complete02 : SourceComplete domains Normalizers.Source03.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source03Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source03.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source03Center03Q8.complete e he hc hs

def pick04 : Fin (maps 5).length → (table 5).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 5).length) : Bool :=
  decide (((domains 5).pencil ((table 5).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes03 4 0 (fun x => (maps 5).get i (Normalizers.Source03.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 5).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 5).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 5).length = (((List.finRange (maps 5).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 5).length,
    ((domains 5).pencil ((table 5).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes03 4 0 (fun x => (maps 5).get i (Normalizers.Source03.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source03.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 5) link03 (templates 5).family hole 4 0
    Normalizers.Source03.normalizer04 Normalizers.Source03.record04.hole_fixed Normalizers.Source03.record04.center_image Normalizers.Source03.record04.star_image
    (maps 5) (maps_complete 5) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 5) (table 5)
    RawClass9.CatalogCodes.codes03 link03 RawClass9.CatalogCodes.checked03
    4 0 Normalizers.Source03.normalizer04 (maps 5) pick04 rows04

theorem complete05 : SourceComplete domains Normalizers.Source03.record05 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source03Center05.complete e he hc hs

theorem complete06 : SourceComplete domains Normalizers.Source03.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source03Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source03.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source03Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source03.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source03Center08Q6.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source03.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source03Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source03.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source03Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source03.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source03Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source03.entries, SourceComplete domains r := by
  simp only [Normalizers.Source03.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source03
