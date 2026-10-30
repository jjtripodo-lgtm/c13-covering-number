import C13Enumeration.Canonical.Normalizers.Source65
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source65
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem complete00 : SourceComplete domains Normalizers.Source65.record00 := by
  intro _ e he hc hs
  exact RawClass9.Source65Center00Q6.complete e he hc hs

def pick01 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes65 1 2 (fun x => (maps 19).get i (Normalizers.Source65.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 19).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes65 1 2 (fun x => (maps 19).get i (Normalizers.Source65.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source65.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link65 (templates 19).family hole 1 2
    Normalizers.Source65.normalizer01 Normalizers.Source65.record01.hole_fixed Normalizers.Source65.record01.center_image Normalizers.Source65.record01.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes65 link65 RawClass9.CatalogCodes.checked65
    1 2 Normalizers.Source65.normalizer01 (maps 19) pick01 rows01

def pick02 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes65 2 6 (fun x => (maps 35).get i (Normalizers.Source65.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 35).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes65 2 6 (fun x => (maps 35).get i (Normalizers.Source65.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source65.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link65 (templates 35).family hole 2 6
    Normalizers.Source65.normalizer02 Normalizers.Source65.record02.hole_fixed Normalizers.Source65.record02.center_image Normalizers.Source65.record02.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes65 link65 RawClass9.CatalogCodes.checked65
    2 6 Normalizers.Source65.normalizer02 (maps 35) pick02 rows02

theorem complete03 : SourceComplete domains Normalizers.Source65.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source65Center03Q8.complete e he hc hs

def pick04 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes65 4 2 (fun x => (maps 19).get i (Normalizers.Source65.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 19).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes65 4 2 (fun x => (maps 19).get i (Normalizers.Source65.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source65.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link65 (templates 19).family hole 4 2
    Normalizers.Source65.normalizer04 Normalizers.Source65.record04.hole_fixed Normalizers.Source65.record04.center_image Normalizers.Source65.record04.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes65 link65 RawClass9.CatalogCodes.checked65
    4 2 Normalizers.Source65.normalizer04 (maps 19) pick04 rows04

theorem complete05 : SourceComplete domains Normalizers.Source65.record05 := by
  intro _ e he hc hs
  exact RawClass9.Source65Center05Q6.complete e he hc hs

theorem complete06 : SourceComplete domains Normalizers.Source65.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source65Center06Q8.complete e he hc hs

def pick07 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩]
def rowCheck07 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick07 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes65 7 6 (fun x => (maps 35).get i (Normalizers.Source65.normalizer07 x))).toFinset)

theorem chunk07_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck07) = true := by decide +kernel
theorem all07 : ((List.finRange (maps 35).length).all rowCheck07) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk07_0
theorem rows07 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick07 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes65 7 6 (fun x => (maps 35).get i (Normalizers.Source65.normalizer07 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all07) i (by simp))

theorem complete07 : SourceComplete domains Normalizers.Source65.record07 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link65 (templates 35).family hole 7 6
    Normalizers.Source65.normalizer07 Normalizers.Source65.record07.hole_fixed Normalizers.Source65.record07.center_image Normalizers.Source65.record07.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes65 link65 RawClass9.CatalogCodes.checked65
    7 6 Normalizers.Source65.normalizer07 (maps 35) pick07 rows07

def pick08 : Fin (maps 60).length → (table 60).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 60).length) : Bool :=
  decide (((domains 60).pencil ((table 60).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes65 8 8 (fun x => (maps 60).get i (Normalizers.Source65.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 60).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 60).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 60).length = (((List.finRange (maps 60).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 60).length,
    ((domains 60).pencil ((table 60).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes65 8 8 (fun x => (maps 60).get i (Normalizers.Source65.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source65.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 60) link65 (templates 60).family hole 8 8
    Normalizers.Source65.normalizer08 Normalizers.Source65.record08.hole_fixed Normalizers.Source65.record08.center_image Normalizers.Source65.record08.star_image
    (maps 60) (maps_complete 60) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 60) (table 60)
    RawClass9.CatalogCodes.codes65 link65 RawClass9.CatalogCodes.checked65
    8 8 Normalizers.Source65.normalizer08 (maps 60) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source65.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source65Center09Q6.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source65.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source65Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source65.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source65Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source65.entries, SourceComplete domains r := by
  simp only [Normalizers.Source65.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source65
