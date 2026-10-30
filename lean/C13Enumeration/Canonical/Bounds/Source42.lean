import C13Enumeration.Canonical.Normalizers.Source42
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source42
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 45).length → (table 45).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 45).length) : Bool :=
  decide (((domains 45).pencil ((table 45).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes42 0 0 (fun x => (maps 45).get i (Normalizers.Source42.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 45).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 45).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 45).length = (((List.finRange (maps 45).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 45).length,
    ((domains 45).pencil ((table 45).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes42 0 0 (fun x => (maps 45).get i (Normalizers.Source42.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source42.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 45) link42 (templates 45).family hole 0 0
    Normalizers.Source42.normalizer00 Normalizers.Source42.record00.hole_fixed Normalizers.Source42.record00.center_image Normalizers.Source42.record00.star_image
    (maps 45) (maps_complete 45) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 45) (table 45)
    RawClass9.CatalogCodes.codes42 link42 RawClass9.CatalogCodes.checked42
    0 0 Normalizers.Source42.normalizer00 (maps 45) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source42.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source42Center01Q8.complete e he hc hs

theorem complete02 : SourceComplete domains Normalizers.Source42.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source42Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source42.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source42Center03Q8.complete e he hc hs

def pick04 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes42 4 4 (fun x => (maps 17).get i (Normalizers.Source42.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 17).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes42 4 4 (fun x => (maps 17).get i (Normalizers.Source42.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source42.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link42 (templates 17).family hole 4 4
    Normalizers.Source42.normalizer04 Normalizers.Source42.record04.hole_fixed Normalizers.Source42.record04.center_image Normalizers.Source42.record04.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes42 link42 RawClass9.CatalogCodes.checked42
    4 4 Normalizers.Source42.normalizer04 (maps 17) pick04 rows04

def pick05 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes42 5 4 (fun x => (maps 17).get i (Normalizers.Source42.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 17).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes42 5 4 (fun x => (maps 17).get i (Normalizers.Source42.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source42.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link42 (templates 17).family hole 5 4
    Normalizers.Source42.normalizer05 Normalizers.Source42.record05.hole_fixed Normalizers.Source42.record05.center_image Normalizers.Source42.record05.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes42 link42 RawClass9.CatalogCodes.checked42
    5 4 Normalizers.Source42.normalizer05 (maps 17) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source42.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source42Center06Q6.complete e he hc hs

def pick07 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck07 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick07 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes42 7 2 (fun x => (maps 19).get i (Normalizers.Source42.normalizer07 x))).toFinset)

theorem chunk07_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck07) = true := by decide +kernel
theorem all07 : ((List.finRange (maps 19).length).all rowCheck07) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk07_0
theorem rows07 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick07 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes42 7 2 (fun x => (maps 19).get i (Normalizers.Source42.normalizer07 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all07) i (by simp))

theorem complete07 : SourceComplete domains Normalizers.Source42.record07 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link42 (templates 19).family hole 7 2
    Normalizers.Source42.normalizer07 Normalizers.Source42.record07.hole_fixed Normalizers.Source42.record07.center_image Normalizers.Source42.record07.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes42 link42 RawClass9.CatalogCodes.checked42
    7 2 Normalizers.Source42.normalizer07 (maps 19) pick07 rows07

theorem complete08 : SourceComplete domains Normalizers.Source42.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source42Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source42.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source42Center09Q8.complete e he hc hs

def pick10 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩]
def rowCheck10 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick10 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes42 10 2 (fun x => (maps 19).get i (Normalizers.Source42.normalizer10 x))).toFinset)

theorem chunk10_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck10) = true := by decide +kernel
theorem all10 : ((List.finRange (maps 19).length).all rowCheck10) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk10_0
theorem rows10 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick10 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes42 10 2 (fun x => (maps 19).get i (Normalizers.Source42.normalizer10 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all10) i (by simp))

theorem complete10 : SourceComplete domains Normalizers.Source42.record10 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link42 (templates 19).family hole 10 2
    Normalizers.Source42.normalizer10 Normalizers.Source42.record10.hole_fixed Normalizers.Source42.record10.center_image Normalizers.Source42.record10.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes42 link42 RawClass9.CatalogCodes.checked42
    10 2 Normalizers.Source42.normalizer10 (maps 19) pick10 rows10

theorem complete11 : SourceComplete domains Normalizers.Source42.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source42Center11Q6.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source42.entries, SourceComplete domains r := by
  simp only [Normalizers.Source42.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source42
