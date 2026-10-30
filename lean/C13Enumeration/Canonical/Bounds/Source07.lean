import C13Enumeration.Canonical.Normalizers.Source07
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source07
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 11).length → (table 11).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 11).length) : Bool :=
  decide (((domains 11).pencil ((table 11).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes07 0 0 (fun x => (maps 11).get i (Normalizers.Source07.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 11).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 11).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 11).length = (((List.finRange (maps 11).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 11).length,
    ((domains 11).pencil ((table 11).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes07 0 0 (fun x => (maps 11).get i (Normalizers.Source07.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source07.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 11) link07 (templates 11).family hole 0 0
    Normalizers.Source07.normalizer00 Normalizers.Source07.record00.hole_fixed Normalizers.Source07.record00.center_image Normalizers.Source07.record00.star_image
    (maps 11) (maps_complete 11) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 11) (table 11)
    RawClass9.CatalogCodes.codes07 link07 RawClass9.CatalogCodes.checked07
    0 0 Normalizers.Source07.normalizer00 (maps 11) pick00 rows00

def pick01 : Fin (maps 9).length → (table 9).Index := ![⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 9).length) : Bool :=
  decide (((domains 9).pencil ((table 9).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes07 1 2 (fun x => (maps 9).get i (Normalizers.Source07.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 9).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 9).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 9).length = (((List.finRange (maps 9).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 9).length,
    ((domains 9).pencil ((table 9).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes07 1 2 (fun x => (maps 9).get i (Normalizers.Source07.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source07.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 9) link07 (templates 9).family hole 1 2
    Normalizers.Source07.normalizer01 Normalizers.Source07.record01.hole_fixed Normalizers.Source07.record01.center_image Normalizers.Source07.record01.star_image
    (maps 9) (maps_complete 9) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 9) (table 9)
    RawClass9.CatalogCodes.codes07 link07 RawClass9.CatalogCodes.checked07
    1 2 Normalizers.Source07.normalizer01 (maps 9) pick01 rows01

def pick02 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes07 2 2 (fun x => (maps 12).get i (Normalizers.Source07.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 12).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes07 2 2 (fun x => (maps 12).get i (Normalizers.Source07.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source07.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link07 (templates 12).family hole 2 2
    Normalizers.Source07.normalizer02 Normalizers.Source07.record02.hole_fixed Normalizers.Source07.record02.center_image Normalizers.Source07.record02.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes07 link07 RawClass9.CatalogCodes.checked07
    2 2 Normalizers.Source07.normalizer02 (maps 12) pick02 rows02

theorem complete03 : SourceComplete domains Normalizers.Source07.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source07Center03Q8.complete e he hc hs

def pick04 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes07 4 2 (fun x => (maps 12).get i (Normalizers.Source07.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 12).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes07 4 2 (fun x => (maps 12).get i (Normalizers.Source07.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source07.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link07 (templates 12).family hole 4 2
    Normalizers.Source07.normalizer04 Normalizers.Source07.record04.hole_fixed Normalizers.Source07.record04.center_image Normalizers.Source07.record04.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes07 link07 RawClass9.CatalogCodes.checked07
    4 2 Normalizers.Source07.normalizer04 (maps 12) pick04 rows04

def pick05 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes07 5 2 (fun x => (maps 12).get i (Normalizers.Source07.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 12).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes07 5 2 (fun x => (maps 12).get i (Normalizers.Source07.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source07.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link07 (templates 12).family hole 5 2
    Normalizers.Source07.normalizer05 Normalizers.Source07.record05.hole_fixed Normalizers.Source07.record05.center_image Normalizers.Source07.record05.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes07 link07 RawClass9.CatalogCodes.checked07
    5 2 Normalizers.Source07.normalizer05 (maps 12) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source07.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source07Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source07.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source07Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source07.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source07Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source07.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source07Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source07.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source07Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source07.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source07Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source07.entries, SourceComplete domains r := by
  simp only [Normalizers.Source07.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source07
