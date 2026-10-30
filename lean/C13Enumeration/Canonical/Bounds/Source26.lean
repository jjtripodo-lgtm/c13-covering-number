import C13Enumeration.Canonical.Normalizers.Source26
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source26
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 26).length → (table 26).Index := ![⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 26).length) : Bool :=
  decide (((domains 26).pencil ((table 26).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes26 0 0 (fun x => (maps 26).get i (Normalizers.Source26.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 26).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 26).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 26).length = (((List.finRange (maps 26).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 26).length,
    ((domains 26).pencil ((table 26).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes26 0 0 (fun x => (maps 26).get i (Normalizers.Source26.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source26.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 26) link26 (templates 26).family hole 0 0
    Normalizers.Source26.normalizer00 Normalizers.Source26.record00.hole_fixed Normalizers.Source26.record00.center_image Normalizers.Source26.record00.star_image
    (maps 26) (maps_complete 26) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 26) (table 26)
    RawClass9.CatalogCodes.codes26 link26 RawClass9.CatalogCodes.checked26
    0 0 Normalizers.Source26.normalizer00 (maps 26) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source26.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source26Center01Q8.complete e he hc hs

theorem complete02 : SourceComplete domains Normalizers.Source26.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source26Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source26.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source26Center03Q8.complete e he hc hs

def pick04 : Fin (maps 27).length → (table 27).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 27).length) : Bool :=
  decide (((domains 27).pencil ((table 27).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes26 4 4 (fun x => (maps 27).get i (Normalizers.Source26.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 27).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 27).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 27).length = (((List.finRange (maps 27).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 27).length,
    ((domains 27).pencil ((table 27).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes26 4 4 (fun x => (maps 27).get i (Normalizers.Source26.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source26.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 27) link26 (templates 27).family hole 4 4
    Normalizers.Source26.normalizer04 Normalizers.Source26.record04.hole_fixed Normalizers.Source26.record04.center_image Normalizers.Source26.record04.star_image
    (maps 27) (maps_complete 27) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 27) (table 27)
    RawClass9.CatalogCodes.codes26 link26 RawClass9.CatalogCodes.checked26
    4 4 Normalizers.Source26.normalizer04 (maps 27) pick04 rows04

def pick05 : Fin (maps 15).length → (table 15).Index := ![⟨⟨0,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 15).length) : Bool :=
  decide (((domains 15).pencil ((table 15).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes26 5 5 (fun x => (maps 15).get i (Normalizers.Source26.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 15).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 15).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 15).length = (((List.finRange (maps 15).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 15).length,
    ((domains 15).pencil ((table 15).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes26 5 5 (fun x => (maps 15).get i (Normalizers.Source26.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source26.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 15) link26 (templates 15).family hole 5 5
    Normalizers.Source26.normalizer05 Normalizers.Source26.record05.hole_fixed Normalizers.Source26.record05.center_image Normalizers.Source26.record05.star_image
    (maps 15) (maps_complete 15) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 15) (table 15)
    RawClass9.CatalogCodes.codes26 link26 RawClass9.CatalogCodes.checked26
    5 5 Normalizers.Source26.normalizer05 (maps 15) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source26.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source26Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source26.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source26Center07Q8.complete e he hc hs

def pick08 : Fin (maps 28).length → (table 28).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 28).length) : Bool :=
  decide (((domains 28).pencil ((table 28).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes26 8 8 (fun x => (maps 28).get i (Normalizers.Source26.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 28).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 28).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 28).length = (((List.finRange (maps 28).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 28).length,
    ((domains 28).pencil ((table 28).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes26 8 8 (fun x => (maps 28).get i (Normalizers.Source26.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source26.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 28) link26 (templates 28).family hole 8 8
    Normalizers.Source26.normalizer08 Normalizers.Source26.record08.hole_fixed Normalizers.Source26.record08.center_image Normalizers.Source26.record08.star_image
    (maps 28) (maps_complete 28) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 28) (table 28)
    RawClass9.CatalogCodes.codes26 link26 RawClass9.CatalogCodes.checked26
    8 8 Normalizers.Source26.normalizer08 (maps 28) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source26.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source26Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source26.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source26Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source26.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source26Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source26.entries, SourceComplete domains r := by
  simp only [Normalizers.Source26.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source26
