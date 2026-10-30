import C13Enumeration.Canonical.Normalizers.Source16
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source16
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 21).length → (table 21).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 21).length) : Bool :=
  decide (((domains 21).pencil ((table 21).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes16 0 0 (fun x => (maps 21).get i (Normalizers.Source16.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 21).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 21).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 21).length = (((List.finRange (maps 21).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 21).length,
    ((domains 21).pencil ((table 21).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes16 0 0 (fun x => (maps 21).get i (Normalizers.Source16.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source16.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 21) link16 (templates 21).family hole 0 0
    Normalizers.Source16.normalizer00 Normalizers.Source16.record00.hole_fixed Normalizers.Source16.record00.center_image Normalizers.Source16.record00.star_image
    (maps 21) (maps_complete 21) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 21) (table 21)
    RawClass9.CatalogCodes.codes16 link16 RawClass9.CatalogCodes.checked16
    0 0 Normalizers.Source16.normalizer00 (maps 21) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source16.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source16Center01Q8.complete e he hc hs

def pick02 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes16 2 2 (fun x => (maps 12).get i (Normalizers.Source16.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 12).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes16 2 2 (fun x => (maps 12).get i (Normalizers.Source16.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source16.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link16 (templates 12).family hole 2 2
    Normalizers.Source16.normalizer02 Normalizers.Source16.record02.hole_fixed Normalizers.Source16.record02.center_image Normalizers.Source16.record02.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes16 link16 RawClass9.CatalogCodes.checked16
    2 2 Normalizers.Source16.normalizer02 (maps 12) pick02 rows02

def pick03 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩]
def rowCheck03 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick03 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes16 3 2 (fun x => (maps 4).get i (Normalizers.Source16.normalizer03 x))).toFinset)

theorem chunk03_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck03) = true := by decide +kernel
theorem all03 : ((List.finRange (maps 4).length).all rowCheck03) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk03_0
theorem rows03 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick03 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes16 3 2 (fun x => (maps 4).get i (Normalizers.Source16.normalizer03 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all03) i (by simp))

theorem complete03 : SourceComplete domains Normalizers.Source16.record03 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link16 (templates 4).family hole 3 2
    Normalizers.Source16.normalizer03 Normalizers.Source16.record03.hole_fixed Normalizers.Source16.record03.center_image Normalizers.Source16.record03.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes16 link16 RawClass9.CatalogCodes.checked16
    3 2 Normalizers.Source16.normalizer03 (maps 4) pick03 rows03

def pick04 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes16 4 2 (fun x => (maps 12).get i (Normalizers.Source16.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 12).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes16 4 2 (fun x => (maps 12).get i (Normalizers.Source16.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source16.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link16 (templates 12).family hole 4 2
    Normalizers.Source16.normalizer04 Normalizers.Source16.record04.hole_fixed Normalizers.Source16.record04.center_image Normalizers.Source16.record04.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes16 link16 RawClass9.CatalogCodes.checked16
    4 2 Normalizers.Source16.normalizer04 (maps 12) pick04 rows04

def pick05 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes16 5 2 (fun x => (maps 12).get i (Normalizers.Source16.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 12).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes16 5 2 (fun x => (maps 12).get i (Normalizers.Source16.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source16.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link16 (templates 12).family hole 5 2
    Normalizers.Source16.normalizer05 Normalizers.Source16.record05.hole_fixed Normalizers.Source16.record05.center_image Normalizers.Source16.record05.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes16 link16 RawClass9.CatalogCodes.checked16
    5 2 Normalizers.Source16.normalizer05 (maps 12) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source16.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source16Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source16.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source16Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source16.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source16Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source16.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source16Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source16.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source16Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source16.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source16Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source16.entries, SourceComplete domains r := by
  simp only [Normalizers.Source16.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source16
