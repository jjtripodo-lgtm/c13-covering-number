import C13Enumeration.Canonical.Normalizers.Source05
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source05
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem complete00 : SourceComplete domains Normalizers.Source05.record00 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source05Center00.complete e he hc hs

theorem complete01 : SourceComplete domains Normalizers.Source05.record01 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source05Center01.complete e he hc hs

def pick02 : Fin (maps 9).length → (table 9).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 9).length) : Bool :=
  decide (((domains 9).pencil ((table 9).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes05 2 2 (fun x => (maps 9).get i (Normalizers.Source05.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 9).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 9).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 9).length = (((List.finRange (maps 9).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 9).length,
    ((domains 9).pencil ((table 9).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes05 2 2 (fun x => (maps 9).get i (Normalizers.Source05.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source05.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 9) link05 (templates 9).family hole 2 2
    Normalizers.Source05.normalizer02 Normalizers.Source05.record02.hole_fixed Normalizers.Source05.record02.center_image Normalizers.Source05.record02.star_image
    (maps 9) (maps_complete 9) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 9) (table 9)
    RawClass9.CatalogCodes.codes05 link05 RawClass9.CatalogCodes.checked05
    2 2 Normalizers.Source05.normalizer02 (maps 9) pick02 rows02

def pick03 : Fin (maps 9).length → (table 9).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck03 (i : Fin (maps 9).length) : Bool :=
  decide (((domains 9).pencil ((table 9).row (pick03 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes05 3 2 (fun x => (maps 9).get i (Normalizers.Source05.normalizer03 x))).toFinset)

theorem chunk03_0 : ((((List.finRange (maps 9).length).drop 0).take 16).all rowCheck03) = true := by decide +kernel
theorem all03 : ((List.finRange (maps 9).length).all rowCheck03) = true := by
  have hsplit : List.finRange (maps 9).length = (((List.finRange (maps 9).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk03_0
theorem rows03 : ∀ i : Fin (maps 9).length,
    ((domains 9).pencil ((table 9).row (pick03 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes05 3 2 (fun x => (maps 9).get i (Normalizers.Source05.normalizer03 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all03) i (by simp))

theorem complete03 : SourceComplete domains Normalizers.Source05.record03 := by
  intro _ e he hc hs
  apply source_center_represented (domains 9) link05 (templates 9).family hole 3 2
    Normalizers.Source05.normalizer03 Normalizers.Source05.record03.hole_fixed Normalizers.Source05.record03.center_image Normalizers.Source05.record03.star_image
    (maps 9) (maps_complete 9) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 9) (table 9)
    RawClass9.CatalogCodes.codes05 link05 RawClass9.CatalogCodes.checked05
    3 2 Normalizers.Source05.normalizer03 (maps 9) pick03 rows03

theorem complete04 : SourceComplete domains Normalizers.Source05.record04 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source05Center04.complete e he hc hs

theorem complete05 : SourceComplete domains Normalizers.Source05.record05 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source05Center05.complete e he hc hs

theorem complete06 : SourceComplete domains Normalizers.Source05.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source05Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source05.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source05Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source05.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source05Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source05.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source05Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source05.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source05Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source05.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source05Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source05.entries, SourceComplete domains r := by
  simp only [Normalizers.Source05.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source05
