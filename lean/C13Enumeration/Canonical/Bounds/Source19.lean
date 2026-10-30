import C13Enumeration.Canonical.Normalizers.Source19
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source19
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes19 0 2 (fun x => (maps 12).get i (Normalizers.Source19.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 12).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes19 0 2 (fun x => (maps 12).get i (Normalizers.Source19.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source19.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link19 (templates 12).family hole 0 2
    Normalizers.Source19.normalizer00 Normalizers.Source19.record00.hole_fixed Normalizers.Source19.record00.center_image Normalizers.Source19.record00.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes19 link19 RawClass9.CatalogCodes.checked19
    0 2 Normalizers.Source19.normalizer00 (maps 12) pick00 rows00

def pick01 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes19 1 2 (fun x => (maps 4).get i (Normalizers.Source19.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 4).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes19 1 2 (fun x => (maps 4).get i (Normalizers.Source19.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source19.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link19 (templates 4).family hole 1 2
    Normalizers.Source19.normalizer01 Normalizers.Source19.record01.hole_fixed Normalizers.Source19.record01.center_image Normalizers.Source19.record01.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes19 link19 RawClass9.CatalogCodes.checked19
    1 2 Normalizers.Source19.normalizer01 (maps 4) pick01 rows01

def pick02 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes19 2 2 (fun x => (maps 12).get i (Normalizers.Source19.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 12).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes19 2 2 (fun x => (maps 12).get i (Normalizers.Source19.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source19.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link19 (templates 12).family hole 2 2
    Normalizers.Source19.normalizer02 Normalizers.Source19.record02.hole_fixed Normalizers.Source19.record02.center_image Normalizers.Source19.record02.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes19 link19 RawClass9.CatalogCodes.checked19
    2 2 Normalizers.Source19.normalizer02 (maps 12) pick02 rows02

def pick03 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩]
def rowCheck03 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick03 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes19 3 2 (fun x => (maps 4).get i (Normalizers.Source19.normalizer03 x))).toFinset)

theorem chunk03_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck03) = true := by decide +kernel
theorem all03 : ((List.finRange (maps 4).length).all rowCheck03) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk03_0
theorem rows03 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick03 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes19 3 2 (fun x => (maps 4).get i (Normalizers.Source19.normalizer03 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all03) i (by simp))

theorem complete03 : SourceComplete domains Normalizers.Source19.record03 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link19 (templates 4).family hole 3 2
    Normalizers.Source19.normalizer03 Normalizers.Source19.record03.hole_fixed Normalizers.Source19.record03.center_image Normalizers.Source19.record03.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes19 link19 RawClass9.CatalogCodes.checked19
    3 2 Normalizers.Source19.normalizer03 (maps 4) pick03 rows03

def pick04 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes19 4 2 (fun x => (maps 12).get i (Normalizers.Source19.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 12).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes19 4 2 (fun x => (maps 12).get i (Normalizers.Source19.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source19.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link19 (templates 12).family hole 4 2
    Normalizers.Source19.normalizer04 Normalizers.Source19.record04.hole_fixed Normalizers.Source19.record04.center_image Normalizers.Source19.record04.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes19 link19 RawClass9.CatalogCodes.checked19
    4 2 Normalizers.Source19.normalizer04 (maps 12) pick04 rows04

def pick05 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes19 5 2 (fun x => (maps 12).get i (Normalizers.Source19.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 12).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes19 5 2 (fun x => (maps 12).get i (Normalizers.Source19.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source19.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link19 (templates 12).family hole 5 2
    Normalizers.Source19.normalizer05 Normalizers.Source19.record05.hole_fixed Normalizers.Source19.record05.center_image Normalizers.Source19.record05.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes19 link19 RawClass9.CatalogCodes.checked19
    5 2 Normalizers.Source19.normalizer05 (maps 12) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source19.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source19Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source19.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source19Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source19.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source19Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source19.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source19Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source19.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source19Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source19.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source19Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source19.entries, SourceComplete domains r := by
  simp only [Normalizers.Source19.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source19
