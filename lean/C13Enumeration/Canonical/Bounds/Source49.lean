import C13Enumeration.Canonical.Normalizers.Source49
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source49
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 18).length → (table 18).Index := ![⟨⟨0,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨37,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 18).length) : Bool :=
  decide (((domains 18).pencil ((table 18).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes49 0 2 (fun x => (maps 18).get i (Normalizers.Source49.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 18).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 18).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 18).length = (((List.finRange (maps 18).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 18).length,
    ((domains 18).pencil ((table 18).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes49 0 2 (fun x => (maps 18).get i (Normalizers.Source49.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source49.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 18) link49 (templates 18).family hole 0 2
    Normalizers.Source49.normalizer00 Normalizers.Source49.record00.hole_fixed Normalizers.Source49.record00.center_image Normalizers.Source49.record00.star_image
    (maps 18) (maps_complete 18) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 18) (table 18)
    RawClass9.CatalogCodes.codes49 link49 RawClass9.CatalogCodes.checked49
    0 2 Normalizers.Source49.normalizer00 (maps 18) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source49.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source49Center01Q8.complete e he hc hs

def pick02 : Fin (maps 10).length → (table 10).Index := ![⟨⟨0,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 10).length) : Bool :=
  decide (((domains 10).pencil ((table 10).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes49 2 2 (fun x => (maps 10).get i (Normalizers.Source49.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 10).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 10).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 10).length = (((List.finRange (maps 10).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 10).length,
    ((domains 10).pencil ((table 10).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes49 2 2 (fun x => (maps 10).get i (Normalizers.Source49.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source49.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 10) link49 (templates 10).family hole 2 2
    Normalizers.Source49.normalizer02 Normalizers.Source49.record02.hole_fixed Normalizers.Source49.record02.center_image Normalizers.Source49.record02.star_image
    (maps 10) (maps_complete 10) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 10) (table 10)
    RawClass9.CatalogCodes.codes49 link49 RawClass9.CatalogCodes.checked49
    2 2 Normalizers.Source49.normalizer02 (maps 10) pick02 rows02

theorem complete03 : SourceComplete domains Normalizers.Source49.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source49Center03Q8.complete e he hc hs

def pick04 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes49 4 4 (fun x => (maps 17).get i (Normalizers.Source49.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 17).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes49 4 4 (fun x => (maps 17).get i (Normalizers.Source49.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source49.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link49 (templates 17).family hole 4 4
    Normalizers.Source49.normalizer04 Normalizers.Source49.record04.hole_fixed Normalizers.Source49.record04.center_image Normalizers.Source49.record04.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes49 link49 RawClass9.CatalogCodes.checked49
    4 4 Normalizers.Source49.normalizer04 (maps 17) pick04 rows04

def pick05 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes49 5 4 (fun x => (maps 17).get i (Normalizers.Source49.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 17).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes49 5 4 (fun x => (maps 17).get i (Normalizers.Source49.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source49.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link49 (templates 17).family hole 5 4
    Normalizers.Source49.normalizer05 Normalizers.Source49.record05.hole_fixed Normalizers.Source49.record05.center_image Normalizers.Source49.record05.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes49 link49 RawClass9.CatalogCodes.checked49
    5 4 Normalizers.Source49.normalizer05 (maps 17) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source49.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source49Center06Q6.complete e he hc hs

def pick07 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩]
def rowCheck07 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick07 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes49 7 6 (fun x => (maps 35).get i (Normalizers.Source49.normalizer07 x))).toFinset)

theorem chunk07_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck07) = true := by decide +kernel
theorem all07 : ((List.finRange (maps 35).length).all rowCheck07) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk07_0
theorem rows07 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick07 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes49 7 6 (fun x => (maps 35).get i (Normalizers.Source49.normalizer07 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all07) i (by simp))

theorem complete07 : SourceComplete domains Normalizers.Source49.record07 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link49 (templates 35).family hole 7 6
    Normalizers.Source49.normalizer07 Normalizers.Source49.record07.hole_fixed Normalizers.Source49.record07.center_image Normalizers.Source49.record07.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes49 link49 RawClass9.CatalogCodes.checked49
    7 6 Normalizers.Source49.normalizer07 (maps 35) pick07 rows07

theorem complete08 : SourceComplete domains Normalizers.Source49.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source49Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source49.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source49Center09Q6.complete e he hc hs

def pick10 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩]
def rowCheck10 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick10 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes49 10 6 (fun x => (maps 35).get i (Normalizers.Source49.normalizer10 x))).toFinset)

theorem chunk10_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck10) = true := by decide +kernel
theorem all10 : ((List.finRange (maps 35).length).all rowCheck10) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk10_0
theorem rows10 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick10 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes49 10 6 (fun x => (maps 35).get i (Normalizers.Source49.normalizer10 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all10) i (by simp))

theorem complete10 : SourceComplete domains Normalizers.Source49.record10 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link49 (templates 35).family hole 10 6
    Normalizers.Source49.normalizer10 Normalizers.Source49.record10.hole_fixed Normalizers.Source49.record10.center_image Normalizers.Source49.record10.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes49 link49 RawClass9.CatalogCodes.checked49
    10 6 Normalizers.Source49.normalizer10 (maps 35) pick10 rows10

theorem complete11 : SourceComplete domains Normalizers.Source49.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source49Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source49.entries, SourceComplete domains r := by
  simp only [Normalizers.Source49.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source49
