import C13Enumeration.Canonical.Normalizers.Source02
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source02
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 3).length → (table 3).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 3).length) : Bool :=
  decide (((domains 3).pencil ((table 3).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes02 0 0 (fun x => (maps 3).get i (Normalizers.Source02.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 3).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 3).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 3).length = (((List.finRange (maps 3).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 3).length,
    ((domains 3).pencil ((table 3).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes02 0 0 (fun x => (maps 3).get i (Normalizers.Source02.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source02.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 3) link02 (templates 3).family hole 0 0
    Normalizers.Source02.normalizer00 Normalizers.Source02.record00.hole_fixed Normalizers.Source02.record00.center_image Normalizers.Source02.record00.star_image
    (maps 3) (maps_complete 3) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 3) (table 3)
    RawClass9.CatalogCodes.codes02 link02 RawClass9.CatalogCodes.checked02
    0 0 Normalizers.Source02.normalizer00 (maps 3) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source02.record01 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source02Center01.complete e he hc hs

def pick02 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes02 2 2 (fun x => (maps 4).get i (Normalizers.Source02.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 4).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes02 2 2 (fun x => (maps 4).get i (Normalizers.Source02.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source02.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link02 (templates 4).family hole 2 2
    Normalizers.Source02.normalizer02 Normalizers.Source02.record02.hole_fixed Normalizers.Source02.record02.center_image Normalizers.Source02.record02.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes02 link02 RawClass9.CatalogCodes.checked02
    2 2 Normalizers.Source02.normalizer02 (maps 4) pick02 rows02

theorem complete03 : SourceComplete domains Normalizers.Source02.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source02Center03Q8.complete e he hc hs

theorem complete04 : SourceComplete domains Normalizers.Source02.record04 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source02Center04.complete e he hc hs

theorem complete05 : SourceComplete domains Normalizers.Source02.record05 := by
  intro _ e he hc hs
  exact DegreeEightPilot.Source02Center05.complete e he hc hs

theorem complete06 : SourceComplete domains Normalizers.Source02.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source02Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source02.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source02Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source02.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source02Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source02.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source02Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source02.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source02Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source02.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source02Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source02.entries, SourceComplete domains r := by
  simp only [Normalizers.Source02.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source02
