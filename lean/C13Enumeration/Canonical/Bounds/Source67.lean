import C13Enumeration.Canonical.Normalizers.Source67
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source67
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem complete00 : SourceComplete domains Normalizers.Source67.record00 := by
  intro _ e he hc hs
  exact RawClass9.Source67Center00Q6.complete e he hc hs

def pick01 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes67 1 6 (fun x => (maps 35).get i (Normalizers.Source67.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 35).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes67 1 6 (fun x => (maps 35).get i (Normalizers.Source67.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source67.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link67 (templates 35).family hole 1 6
    Normalizers.Source67.normalizer01 Normalizers.Source67.record01.hole_fixed Normalizers.Source67.record01.center_image Normalizers.Source67.record01.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes67 link67 RawClass9.CatalogCodes.checked67
    1 6 Normalizers.Source67.normalizer01 (maps 35) pick01 rows01

theorem complete02 : SourceComplete domains Normalizers.Source67.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source67Center02Q8.complete e he hc hs

def pick03 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩]
def rowCheck03 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick03 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes67 3 6 (fun x => (maps 35).get i (Normalizers.Source67.normalizer03 x))).toFinset)

theorem chunk03_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck03) = true := by decide +kernel
theorem all03 : ((List.finRange (maps 35).length).all rowCheck03) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk03_0
theorem rows03 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick03 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes67 3 6 (fun x => (maps 35).get i (Normalizers.Source67.normalizer03 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all03) i (by simp))

theorem complete03 : SourceComplete domains Normalizers.Source67.record03 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link67 (templates 35).family hole 3 6
    Normalizers.Source67.normalizer03 Normalizers.Source67.record03.hole_fixed Normalizers.Source67.record03.center_image Normalizers.Source67.record03.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes67 link67 RawClass9.CatalogCodes.checked67
    3 6 Normalizers.Source67.normalizer03 (maps 35) pick03 rows03

def pick04 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes67 4 6 (fun x => (maps 35).get i (Normalizers.Source67.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 35).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes67 4 6 (fun x => (maps 35).get i (Normalizers.Source67.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source67.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link67 (templates 35).family hole 4 6
    Normalizers.Source67.normalizer04 Normalizers.Source67.record04.hole_fixed Normalizers.Source67.record04.center_image Normalizers.Source67.record04.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes67 link67 RawClass9.CatalogCodes.checked67
    4 6 Normalizers.Source67.normalizer04 (maps 35) pick04 rows04

theorem complete05 : SourceComplete domains Normalizers.Source67.record05 := by
  intro _ e he hc hs
  exact RawClass9.Source67Center05Q8.complete e he hc hs

def pick06 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩]
def rowCheck06 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick06 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes67 6 6 (fun x => (maps 35).get i (Normalizers.Source67.normalizer06 x))).toFinset)

theorem chunk06_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck06) = true := by decide +kernel
theorem all06 : ((List.finRange (maps 35).length).all rowCheck06) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk06_0
theorem rows06 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick06 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes67 6 6 (fun x => (maps 35).get i (Normalizers.Source67.normalizer06 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all06) i (by simp))

theorem complete06 : SourceComplete domains Normalizers.Source67.record06 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link67 (templates 35).family hole 6 6
    Normalizers.Source67.normalizer06 Normalizers.Source67.record06.hole_fixed Normalizers.Source67.record06.center_image Normalizers.Source67.record06.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes67 link67 RawClass9.CatalogCodes.checked67
    6 6 Normalizers.Source67.normalizer06 (maps 35) pick06 rows06

theorem complete07 : SourceComplete domains Normalizers.Source67.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source67Center07Q6.complete e he hc hs

def pick08 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes67 8 6 (fun x => (maps 35).get i (Normalizers.Source67.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 35).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes67 8 6 (fun x => (maps 35).get i (Normalizers.Source67.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source67.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link67 (templates 35).family hole 8 6
    Normalizers.Source67.normalizer08 Normalizers.Source67.record08.hole_fixed Normalizers.Source67.record08.center_image Normalizers.Source67.record08.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes67 link67 RawClass9.CatalogCodes.checked67
    8 6 Normalizers.Source67.normalizer08 (maps 35) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source67.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source67Center09Q6.complete e he hc hs

def pick10 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩]
def rowCheck10 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick10 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes67 10 6 (fun x => (maps 35).get i (Normalizers.Source67.normalizer10 x))).toFinset)

theorem chunk10_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck10) = true := by decide +kernel
theorem all10 : ((List.finRange (maps 35).length).all rowCheck10) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk10_0
theorem rows10 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick10 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes67 10 6 (fun x => (maps 35).get i (Normalizers.Source67.normalizer10 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all10) i (by simp))

theorem complete10 : SourceComplete domains Normalizers.Source67.record10 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link67 (templates 35).family hole 10 6
    Normalizers.Source67.normalizer10 Normalizers.Source67.record10.hole_fixed Normalizers.Source67.record10.center_image Normalizers.Source67.record10.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes67 link67 RawClass9.CatalogCodes.checked67
    10 6 Normalizers.Source67.normalizer10 (maps 35) pick10 rows10

theorem complete11 : SourceComplete domains Normalizers.Source67.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source67Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source67.entries, SourceComplete domains r := by
  simp only [Normalizers.Source67.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source67
