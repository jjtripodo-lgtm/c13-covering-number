import C13Enumeration.Canonical.Normalizers.Source33
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source33
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨27,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes33 0 2 (fun x => (maps 19).get i (Normalizers.Source33.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 19).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes33 0 2 (fun x => (maps 19).get i (Normalizers.Source33.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source33.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link33 (templates 19).family hole 0 2
    Normalizers.Source33.normalizer00 Normalizers.Source33.record00.hole_fixed Normalizers.Source33.record00.center_image Normalizers.Source33.record00.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes33 link33 RawClass9.CatalogCodes.checked33
    0 2 Normalizers.Source33.normalizer00 (maps 19) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source33.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source33Center01Q8.complete e he hc hs

def pick02 : Fin (maps 8).length → (table 8).Index := ![⟨⟨0,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨27,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 8).length) : Bool :=
  decide (((domains 8).pencil ((table 8).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes33 2 6 (fun x => (maps 8).get i (Normalizers.Source33.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 8).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 8).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 8).length = (((List.finRange (maps 8).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 8).length,
    ((domains 8).pencil ((table 8).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes33 2 6 (fun x => (maps 8).get i (Normalizers.Source33.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source33.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 8) link33 (templates 8).family hole 2 6
    Normalizers.Source33.normalizer02 Normalizers.Source33.record02.hole_fixed Normalizers.Source33.record02.center_image Normalizers.Source33.record02.star_image
    (maps 8) (maps_complete 8) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 8) (table 8)
    RawClass9.CatalogCodes.codes33 link33 RawClass9.CatalogCodes.checked33
    2 6 Normalizers.Source33.normalizer02 (maps 8) pick02 rows02

theorem complete03 : SourceComplete domains Normalizers.Source33.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source33Center03Q8.complete e he hc hs

def pick04 : Fin (maps 14).length → (table 14).Index := ![⟨⟨0,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 14).length) : Bool :=
  decide (((domains 14).pencil ((table 14).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes33 4 4 (fun x => (maps 14).get i (Normalizers.Source33.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 14).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 14).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 14).length = (((List.finRange (maps 14).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 14).length,
    ((domains 14).pencil ((table 14).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes33 4 4 (fun x => (maps 14).get i (Normalizers.Source33.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source33.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 14) link33 (templates 14).family hole 4 4
    Normalizers.Source33.normalizer04 Normalizers.Source33.record04.hole_fixed Normalizers.Source33.record04.center_image Normalizers.Source33.record04.star_image
    (maps 14) (maps_complete 14) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 14) (table 14)
    RawClass9.CatalogCodes.codes33 link33 RawClass9.CatalogCodes.checked33
    4 4 Normalizers.Source33.normalizer04 (maps 14) pick04 rows04

def pick05 : Fin (maps 37).length → (table 37).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 37).length) : Bool :=
  decide (((domains 37).pencil ((table 37).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes33 5 5 (fun x => (maps 37).get i (Normalizers.Source33.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 37).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 37).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 37).length = (((List.finRange (maps 37).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 37).length,
    ((domains 37).pencil ((table 37).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes33 5 5 (fun x => (maps 37).get i (Normalizers.Source33.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source33.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 37) link33 (templates 37).family hole 5 5
    Normalizers.Source33.normalizer05 Normalizers.Source33.record05.hole_fixed Normalizers.Source33.record05.center_image Normalizers.Source33.record05.star_image
    (maps 37) (maps_complete 37) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 37) (table 37)
    RawClass9.CatalogCodes.codes33 link33 RawClass9.CatalogCodes.checked33
    5 5 Normalizers.Source33.normalizer05 (maps 37) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source33.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source33Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source33.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source33Center07Q8.complete e he hc hs

def pick08 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨12,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes33 8 6 (fun x => (maps 35).get i (Normalizers.Source33.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 35).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes33 8 6 (fun x => (maps 35).get i (Normalizers.Source33.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source33.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link33 (templates 35).family hole 8 6
    Normalizers.Source33.normalizer08 Normalizers.Source33.record08.hole_fixed Normalizers.Source33.record08.center_image Normalizers.Source33.record08.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes33 link33 RawClass9.CatalogCodes.checked33
    8 6 Normalizers.Source33.normalizer08 (maps 35) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source33.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source33Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source33.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source33Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source33.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source33Center11Q6.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source33.entries, SourceComplete domains r := by
  simp only [Normalizers.Source33.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source33
