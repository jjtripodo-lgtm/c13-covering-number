import C13Enumeration.Canonical.Normalizers.Source14
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source14
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 9).length → (table 9).Index := ![⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 9).length) : Bool :=
  decide (((domains 9).pencil ((table 9).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes14 0 2 (fun x => (maps 9).get i (Normalizers.Source14.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 9).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 9).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 9).length = (((List.finRange (maps 9).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 9).length,
    ((domains 9).pencil ((table 9).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes14 0 2 (fun x => (maps 9).get i (Normalizers.Source14.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source14.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 9) link14 (templates 9).family hole 0 2
    Normalizers.Source14.normalizer00 Normalizers.Source14.record00.hole_fixed Normalizers.Source14.record00.center_image Normalizers.Source14.record00.star_image
    (maps 9) (maps_complete 9) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 9) (table 9)
    RawClass9.CatalogCodes.codes14 link14 RawClass9.CatalogCodes.checked14
    0 2 Normalizers.Source14.normalizer00 (maps 9) pick00 rows00

def pick01 : Fin (maps 9).length → (table 9).Index := ![⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 9).length) : Bool :=
  decide (((domains 9).pencil ((table 9).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes14 1 2 (fun x => (maps 9).get i (Normalizers.Source14.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 9).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 9).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 9).length = (((List.finRange (maps 9).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 9).length,
    ((domains 9).pencil ((table 9).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes14 1 2 (fun x => (maps 9).get i (Normalizers.Source14.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source14.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 9) link14 (templates 9).family hole 1 2
    Normalizers.Source14.normalizer01 Normalizers.Source14.record01.hole_fixed Normalizers.Source14.record01.center_image Normalizers.Source14.record01.star_image
    (maps 9) (maps_complete 9) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 9) (table 9)
    RawClass9.CatalogCodes.codes14 link14 RawClass9.CatalogCodes.checked14
    1 2 Normalizers.Source14.normalizer01 (maps 9) pick01 rows01

theorem complete02 : SourceComplete domains Normalizers.Source14.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source14Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source14.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source14Center03Q8.complete e he hc hs

def pick04 : Fin (maps 9).length → (table 9).Index := ![⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 9).length) : Bool :=
  decide (((domains 9).pencil ((table 9).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes14 4 2 (fun x => (maps 9).get i (Normalizers.Source14.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 9).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 9).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 9).length = (((List.finRange (maps 9).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 9).length,
    ((domains 9).pencil ((table 9).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes14 4 2 (fun x => (maps 9).get i (Normalizers.Source14.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source14.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 9) link14 (templates 9).family hole 4 2
    Normalizers.Source14.normalizer04 Normalizers.Source14.record04.hole_fixed Normalizers.Source14.record04.center_image Normalizers.Source14.record04.star_image
    (maps 9) (maps_complete 9) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 9) (table 9)
    RawClass9.CatalogCodes.codes14 link14 RawClass9.CatalogCodes.checked14
    4 2 Normalizers.Source14.normalizer04 (maps 9) pick04 rows04

def pick05 : Fin (maps 9).length → (table 9).Index := ![⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 9).length) : Bool :=
  decide (((domains 9).pencil ((table 9).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes14 5 2 (fun x => (maps 9).get i (Normalizers.Source14.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 9).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 9).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 9).length = (((List.finRange (maps 9).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 9).length,
    ((domains 9).pencil ((table 9).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes14 5 2 (fun x => (maps 9).get i (Normalizers.Source14.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source14.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 9) link14 (templates 9).family hole 5 2
    Normalizers.Source14.normalizer05 Normalizers.Source14.record05.hole_fixed Normalizers.Source14.record05.center_image Normalizers.Source14.record05.star_image
    (maps 9) (maps_complete 9) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 9) (table 9)
    RawClass9.CatalogCodes.codes14 link14 RawClass9.CatalogCodes.checked14
    5 2 Normalizers.Source14.normalizer05 (maps 9) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source14.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source14Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source14.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source14Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source14.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source14Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source14.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source14Center09Q8.complete e he hc hs

def pick10 : Fin (maps 9).length → (table 9).Index := ![⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩]
def rowCheck10 (i : Fin (maps 9).length) : Bool :=
  decide (((domains 9).pencil ((table 9).row (pick10 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes14 10 2 (fun x => (maps 9).get i (Normalizers.Source14.normalizer10 x))).toFinset)

theorem chunk10_0 : ((((List.finRange (maps 9).length).drop 0).take 16).all rowCheck10) = true := by decide +kernel
theorem all10 : ((List.finRange (maps 9).length).all rowCheck10) = true := by
  have hsplit : List.finRange (maps 9).length = (((List.finRange (maps 9).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk10_0
theorem rows10 : ∀ i : Fin (maps 9).length,
    ((domains 9).pencil ((table 9).row (pick10 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes14 10 2 (fun x => (maps 9).get i (Normalizers.Source14.normalizer10 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all10) i (by simp))

theorem complete10 : SourceComplete domains Normalizers.Source14.record10 := by
  intro _ e he hc hs
  apply source_center_represented (domains 9) link14 (templates 9).family hole 10 2
    Normalizers.Source14.normalizer10 Normalizers.Source14.record10.hole_fixed Normalizers.Source14.record10.center_image Normalizers.Source14.record10.star_image
    (maps 9) (maps_complete 9) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 9) (table 9)
    RawClass9.CatalogCodes.codes14 link14 RawClass9.CatalogCodes.checked14
    10 2 Normalizers.Source14.normalizer10 (maps 9) pick10 rows10

def pick11 : Fin (maps 9).length → (table 9).Index := ![⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩]
def rowCheck11 (i : Fin (maps 9).length) : Bool :=
  decide (((domains 9).pencil ((table 9).row (pick11 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes14 11 2 (fun x => (maps 9).get i (Normalizers.Source14.normalizer11 x))).toFinset)

theorem chunk11_0 : ((((List.finRange (maps 9).length).drop 0).take 16).all rowCheck11) = true := by decide +kernel
theorem all11 : ((List.finRange (maps 9).length).all rowCheck11) = true := by
  have hsplit : List.finRange (maps 9).length = (((List.finRange (maps 9).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk11_0
theorem rows11 : ∀ i : Fin (maps 9).length,
    ((domains 9).pencil ((table 9).row (pick11 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes14 11 2 (fun x => (maps 9).get i (Normalizers.Source14.normalizer11 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all11) i (by simp))

theorem complete11 : SourceComplete domains Normalizers.Source14.record11 := by
  intro _ e he hc hs
  apply source_center_represented (domains 9) link14 (templates 9).family hole 11 2
    Normalizers.Source14.normalizer11 Normalizers.Source14.record11.hole_fixed Normalizers.Source14.record11.center_image Normalizers.Source14.record11.star_image
    (maps 9) (maps_complete 9) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 9) (table 9)
    RawClass9.CatalogCodes.codes14 link14 RawClass9.CatalogCodes.checked14
    11 2 Normalizers.Source14.normalizer11 (maps 9) pick11 rows11

theorem entries_complete : ∀ r ∈ Normalizers.Source14.entries, SourceComplete domains r := by
  simp only [Normalizers.Source14.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source14
