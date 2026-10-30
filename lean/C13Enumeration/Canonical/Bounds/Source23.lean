import C13Enumeration.Canonical.Normalizers.Source23
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source23
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨12,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes23 0 2 (fun x => (maps 4).get i (Normalizers.Source23.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 4).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes23 0 2 (fun x => (maps 4).get i (Normalizers.Source23.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source23.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link23 (templates 4).family hole 0 2
    Normalizers.Source23.normalizer00 Normalizers.Source23.record00.hole_fixed Normalizers.Source23.record00.center_image Normalizers.Source23.record00.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes23 link23 RawClass9.CatalogCodes.checked23
    0 2 Normalizers.Source23.normalizer00 (maps 4) pick00 rows00

def pick01 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes23 1 2 (fun x => (maps 19).get i (Normalizers.Source23.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 19).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes23 1 2 (fun x => (maps 19).get i (Normalizers.Source23.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source23.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link23 (templates 19).family hole 1 2
    Normalizers.Source23.normalizer01 Normalizers.Source23.record01.hole_fixed Normalizers.Source23.record01.center_image Normalizers.Source23.record01.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes23 link23 RawClass9.CatalogCodes.checked23
    1 2 Normalizers.Source23.normalizer01 (maps 19) pick01 rows01

def pick02 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes23 2 2 (fun x => (maps 4).get i (Normalizers.Source23.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 4).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes23 2 2 (fun x => (maps 4).get i (Normalizers.Source23.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source23.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link23 (templates 4).family hole 2 2
    Normalizers.Source23.normalizer02 Normalizers.Source23.record02.hole_fixed Normalizers.Source23.record02.center_image Normalizers.Source23.record02.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes23 link23 RawClass9.CatalogCodes.checked23
    2 2 Normalizers.Source23.normalizer02 (maps 4) pick02 rows02

theorem complete03 : SourceComplete domains Normalizers.Source23.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source23Center03Q8.complete e he hc hs

def pick04 : Fin (maps 15).length → (table 15).Index := ![⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 15).length) : Bool :=
  decide (((domains 15).pencil ((table 15).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes23 4 5 (fun x => (maps 15).get i (Normalizers.Source23.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 15).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 15).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 15).length = (((List.finRange (maps 15).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 15).length,
    ((domains 15).pencil ((table 15).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes23 4 5 (fun x => (maps 15).get i (Normalizers.Source23.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source23.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 15) link23 (templates 15).family hole 4 5
    Normalizers.Source23.normalizer04 Normalizers.Source23.record04.hole_fixed Normalizers.Source23.record04.center_image Normalizers.Source23.record04.star_image
    (maps 15) (maps_complete 15) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 15) (table 15)
    RawClass9.CatalogCodes.codes23 link23 RawClass9.CatalogCodes.checked23
    4 5 Normalizers.Source23.normalizer04 (maps 15) pick04 rows04

def pick05 : Fin (maps 14).length → (table 14).Index := ![⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 14).length) : Bool :=
  decide (((domains 14).pencil ((table 14).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes23 5 4 (fun x => (maps 14).get i (Normalizers.Source23.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 14).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 14).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 14).length = (((List.finRange (maps 14).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 14).length,
    ((domains 14).pencil ((table 14).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes23 5 4 (fun x => (maps 14).get i (Normalizers.Source23.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source23.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 14) link23 (templates 14).family hole 5 4
    Normalizers.Source23.normalizer05 Normalizers.Source23.record05.hole_fixed Normalizers.Source23.record05.center_image Normalizers.Source23.record05.star_image
    (maps 14) (maps_complete 14) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 14) (table 14)
    RawClass9.CatalogCodes.codes23 link23 RawClass9.CatalogCodes.checked23
    5 4 Normalizers.Source23.normalizer05 (maps 14) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source23.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source23Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source23.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source23Center07Q8.complete e he hc hs

def pick08 : Fin (maps 10).length → (table 10).Index := ![⟨⟨0,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 10).length) : Bool :=
  decide (((domains 10).pencil ((table 10).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes23 8 2 (fun x => (maps 10).get i (Normalizers.Source23.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 10).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 10).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 10).length = (((List.finRange (maps 10).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 10).length,
    ((domains 10).pencil ((table 10).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes23 8 2 (fun x => (maps 10).get i (Normalizers.Source23.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source23.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 10) link23 (templates 10).family hole 8 2
    Normalizers.Source23.normalizer08 Normalizers.Source23.record08.hole_fixed Normalizers.Source23.record08.center_image Normalizers.Source23.record08.star_image
    (maps 10) (maps_complete 10) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 10) (table 10)
    RawClass9.CatalogCodes.codes23 link23 RawClass9.CatalogCodes.checked23
    8 2 Normalizers.Source23.normalizer08 (maps 10) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source23.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source23Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source23.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source23Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source23.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source23Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source23.entries, SourceComplete domains r := by
  simp only [Normalizers.Source23.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source23
