import C13Enumeration.Canonical.Normalizers.Source51
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source51
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 18).length → (table 18).Index := ![⟨⟨0,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨40,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 18).length) : Bool :=
  decide (((domains 18).pencil ((table 18).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes51 0 2 (fun x => (maps 18).get i (Normalizers.Source51.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 18).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 18).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 18).length = (((List.finRange (maps 18).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 18).length,
    ((domains 18).pencil ((table 18).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes51 0 2 (fun x => (maps 18).get i (Normalizers.Source51.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source51.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 18) link51 (templates 18).family hole 0 2
    Normalizers.Source51.normalizer00 Normalizers.Source51.record00.hole_fixed Normalizers.Source51.record00.center_image Normalizers.Source51.record00.star_image
    (maps 18) (maps_complete 18) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 18) (table 18)
    RawClass9.CatalogCodes.codes51 link51 RawClass9.CatalogCodes.checked51
    0 2 Normalizers.Source51.normalizer00 (maps 18) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source51.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source51Center01Q8.complete e he hc hs

theorem complete02 : SourceComplete domains Normalizers.Source51.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source51Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source51.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source51Center03Q8.complete e he hc hs

def pick04 : Fin (maps 50).length → (table 50).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 50).length) : Bool :=
  decide (((domains 50).pencil ((table 50).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes51 4 4 (fun x => (maps 50).get i (Normalizers.Source51.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 50).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 50).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 50).length = (((List.finRange (maps 50).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 50).length,
    ((domains 50).pencil ((table 50).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes51 4 4 (fun x => (maps 50).get i (Normalizers.Source51.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source51.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 50) link51 (templates 50).family hole 4 4
    Normalizers.Source51.normalizer04 Normalizers.Source51.record04.hole_fixed Normalizers.Source51.record04.center_image Normalizers.Source51.record04.star_image
    (maps 50) (maps_complete 50) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 50) (table 50)
    RawClass9.CatalogCodes.codes51 link51 RawClass9.CatalogCodes.checked51
    4 4 Normalizers.Source51.normalizer04 (maps 50) pick04 rows04

def pick05 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes51 5 4 (fun x => (maps 17).get i (Normalizers.Source51.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 17).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes51 5 4 (fun x => (maps 17).get i (Normalizers.Source51.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source51.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link51 (templates 17).family hole 5 4
    Normalizers.Source51.normalizer05 Normalizers.Source51.record05.hole_fixed Normalizers.Source51.record05.center_image Normalizers.Source51.record05.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes51 link51 RawClass9.CatalogCodes.checked51
    5 4 Normalizers.Source51.normalizer05 (maps 17) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source51.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source51Center06Q6.complete e he hc hs

def pick07 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩]
def rowCheck07 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick07 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes51 7 4 (fun x => (maps 17).get i (Normalizers.Source51.normalizer07 x))).toFinset)

theorem chunk07_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck07) = true := by decide +kernel
theorem all07 : ((List.finRange (maps 17).length).all rowCheck07) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk07_0
theorem rows07 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick07 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes51 7 4 (fun x => (maps 17).get i (Normalizers.Source51.normalizer07 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all07) i (by simp))

theorem complete07 : SourceComplete domains Normalizers.Source51.record07 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link51 (templates 17).family hole 7 4
    Normalizers.Source51.normalizer07 Normalizers.Source51.record07.hole_fixed Normalizers.Source51.record07.center_image Normalizers.Source51.record07.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes51 link51 RawClass9.CatalogCodes.checked51
    7 4 Normalizers.Source51.normalizer07 (maps 17) pick07 rows07

theorem complete08 : SourceComplete domains Normalizers.Source51.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source51Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source51.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source51Center09Q8.complete e he hc hs

def pick10 : Fin (maps 18).length → (table 18).Index := ![⟨⟨0,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨40,by decide +kernel⟩⟩]
def rowCheck10 (i : Fin (maps 18).length) : Bool :=
  decide (((domains 18).pencil ((table 18).row (pick10 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes51 10 2 (fun x => (maps 18).get i (Normalizers.Source51.normalizer10 x))).toFinset)

theorem chunk10_0 : ((((List.finRange (maps 18).length).drop 0).take 16).all rowCheck10) = true := by decide +kernel
theorem all10 : ((List.finRange (maps 18).length).all rowCheck10) = true := by
  have hsplit : List.finRange (maps 18).length = (((List.finRange (maps 18).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk10_0
theorem rows10 : ∀ i : Fin (maps 18).length,
    ((domains 18).pencil ((table 18).row (pick10 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes51 10 2 (fun x => (maps 18).get i (Normalizers.Source51.normalizer10 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all10) i (by simp))

theorem complete10 : SourceComplete domains Normalizers.Source51.record10 := by
  intro _ e he hc hs
  apply source_center_represented (domains 18) link51 (templates 18).family hole 10 2
    Normalizers.Source51.normalizer10 Normalizers.Source51.record10.hole_fixed Normalizers.Source51.record10.center_image Normalizers.Source51.record10.star_image
    (maps 18) (maps_complete 18) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 18) (table 18)
    RawClass9.CatalogCodes.codes51 link51 RawClass9.CatalogCodes.checked51
    10 2 Normalizers.Source51.normalizer10 (maps 18) pick10 rows10

theorem complete11 : SourceComplete domains Normalizers.Source51.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source51Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source51.entries, SourceComplete domains r := by
  simp only [Normalizers.Source51.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source51
