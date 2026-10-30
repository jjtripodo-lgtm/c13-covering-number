import C13Enumeration.Canonical.Normalizers.Source66
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source66
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem complete00 : SourceComplete domains Normalizers.Source66.record00 := by
  intro _ e he hc hs
  exact RawClass9.Source66Center00Q6.complete e he hc hs

def pick01 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes66 1 6 (fun x => (maps 35).get i (Normalizers.Source66.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 35).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes66 1 6 (fun x => (maps 35).get i (Normalizers.Source66.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source66.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link66 (templates 35).family hole 1 6
    Normalizers.Source66.normalizer01 Normalizers.Source66.record01.hole_fixed Normalizers.Source66.record01.center_image Normalizers.Source66.record01.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes66 link66 RawClass9.CatalogCodes.checked66
    1 6 Normalizers.Source66.normalizer01 (maps 35) pick01 rows01

def pick02 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes66 2 6 (fun x => (maps 35).get i (Normalizers.Source66.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 35).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes66 2 6 (fun x => (maps 35).get i (Normalizers.Source66.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source66.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link66 (templates 35).family hole 2 6
    Normalizers.Source66.normalizer02 Normalizers.Source66.record02.hole_fixed Normalizers.Source66.record02.center_image Normalizers.Source66.record02.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes66 link66 RawClass9.CatalogCodes.checked66
    2 6 Normalizers.Source66.normalizer02 (maps 35) pick02 rows02

theorem complete03 : SourceComplete domains Normalizers.Source66.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source66Center03Q8.complete e he hc hs

def pick04 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes66 4 6 (fun x => (maps 35).get i (Normalizers.Source66.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 35).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes66 4 6 (fun x => (maps 35).get i (Normalizers.Source66.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source66.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link66 (templates 35).family hole 4 6
    Normalizers.Source66.normalizer04 Normalizers.Source66.record04.hole_fixed Normalizers.Source66.record04.center_image Normalizers.Source66.record04.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes66 link66 RawClass9.CatalogCodes.checked66
    4 6 Normalizers.Source66.normalizer04 (maps 35) pick04 rows04

def pick05 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes66 5 6 (fun x => (maps 35).get i (Normalizers.Source66.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 35).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes66 5 6 (fun x => (maps 35).get i (Normalizers.Source66.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source66.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link66 (templates 35).family hole 5 6
    Normalizers.Source66.normalizer05 Normalizers.Source66.record05.hole_fixed Normalizers.Source66.record05.center_image Normalizers.Source66.record05.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes66 link66 RawClass9.CatalogCodes.checked66
    5 6 Normalizers.Source66.normalizer05 (maps 35) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source66.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source66Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source66.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source66Center07Q6.complete e he hc hs

def pick08 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes66 8 6 (fun x => (maps 35).get i (Normalizers.Source66.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 35).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes66 8 6 (fun x => (maps 35).get i (Normalizers.Source66.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source66.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link66 (templates 35).family hole 8 6
    Normalizers.Source66.normalizer08 Normalizers.Source66.record08.hole_fixed Normalizers.Source66.record08.center_image Normalizers.Source66.record08.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes66 link66 RawClass9.CatalogCodes.checked66
    8 6 Normalizers.Source66.normalizer08 (maps 35) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source66.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source66Center09Q8.complete e he hc hs

def pick10 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩]
def rowCheck10 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick10 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes66 10 6 (fun x => (maps 35).get i (Normalizers.Source66.normalizer10 x))).toFinset)

theorem chunk10_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck10) = true := by decide +kernel
theorem all10 : ((List.finRange (maps 35).length).all rowCheck10) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk10_0
theorem rows10 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick10 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes66 10 6 (fun x => (maps 35).get i (Normalizers.Source66.normalizer10 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all10) i (by simp))

theorem complete10 : SourceComplete domains Normalizers.Source66.record10 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link66 (templates 35).family hole 10 6
    Normalizers.Source66.normalizer10 Normalizers.Source66.record10.hole_fixed Normalizers.Source66.record10.center_image Normalizers.Source66.record10.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes66 link66 RawClass9.CatalogCodes.checked66
    10 6 Normalizers.Source66.normalizer10 (maps 35) pick10 rows10

theorem complete11 : SourceComplete domains Normalizers.Source66.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source66Center11Q6.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source66.entries, SourceComplete domains r := by
  simp only [Normalizers.Source66.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source66
