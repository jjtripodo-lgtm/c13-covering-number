import C13Enumeration.Canonical.Normalizers.Source06
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source06
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem complete00 : SourceComplete domains Normalizers.Source06.record00 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source06Center00.complete e he hc hs

theorem complete01 : SourceComplete domains Normalizers.Source06.record01 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source06Center01.complete e he hc hs

def pick02 : Fin (maps 10).length → (table 10).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 10).length) : Bool :=
  decide (((domains 10).pencil ((table 10).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes06 2 2 (fun x => (maps 10).get i (Normalizers.Source06.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 10).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 10).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 10).length = (((List.finRange (maps 10).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 10).length,
    ((domains 10).pencil ((table 10).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes06 2 2 (fun x => (maps 10).get i (Normalizers.Source06.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source06.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 10) link06 (templates 10).family hole 2 2
    Normalizers.Source06.normalizer02 Normalizers.Source06.record02.hole_fixed Normalizers.Source06.record02.center_image Normalizers.Source06.record02.star_image
    (maps 10) (maps_complete 10) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 10) (table 10)
    RawClass9.CatalogCodes.codes06 link06 RawClass9.CatalogCodes.checked06
    2 2 Normalizers.Source06.normalizer02 (maps 10) pick02 rows02

theorem complete03 : SourceComplete domains Normalizers.Source06.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source06Center03Q8.complete e he hc hs

theorem complete04 : SourceComplete domains Normalizers.Source06.record04 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source06Center04.complete e he hc hs

theorem complete05 : SourceComplete domains Normalizers.Source06.record05 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source06Center05.complete e he hc hs

def pick06 : Fin (maps 10).length → (table 10).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩]
def rowCheck06 (i : Fin (maps 10).length) : Bool :=
  decide (((domains 10).pencil ((table 10).row (pick06 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes06 6 2 (fun x => (maps 10).get i (Normalizers.Source06.normalizer06 x))).toFinset)

theorem chunk06_0 : ((((List.finRange (maps 10).length).drop 0).take 16).all rowCheck06) = true := by decide +kernel
theorem all06 : ((List.finRange (maps 10).length).all rowCheck06) = true := by
  have hsplit : List.finRange (maps 10).length = (((List.finRange (maps 10).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk06_0
theorem rows06 : ∀ i : Fin (maps 10).length,
    ((domains 10).pencil ((table 10).row (pick06 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes06 6 2 (fun x => (maps 10).get i (Normalizers.Source06.normalizer06 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all06) i (by simp))

theorem complete06 : SourceComplete domains Normalizers.Source06.record06 := by
  intro _ e he hc hs
  apply source_center_represented (domains 10) link06 (templates 10).family hole 6 2
    Normalizers.Source06.normalizer06 Normalizers.Source06.record06.hole_fixed Normalizers.Source06.record06.center_image Normalizers.Source06.record06.star_image
    (maps 10) (maps_complete 10) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 10) (table 10)
    RawClass9.CatalogCodes.codes06 link06 RawClass9.CatalogCodes.checked06
    6 2 Normalizers.Source06.normalizer06 (maps 10) pick06 rows06

theorem complete07 : SourceComplete domains Normalizers.Source06.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source06Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source06.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source06Center08Q6.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source06.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source06Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source06.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source06Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source06.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source06Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source06.entries, SourceComplete domains r := by
  simp only [Normalizers.Source06.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source06
