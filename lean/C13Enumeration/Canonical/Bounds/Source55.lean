import C13Enumeration.Canonical.Normalizers.Source55
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source55
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 28).length → (table 28).Index := ![⟨⟨0,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨27,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨37,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 28).length) : Bool :=
  decide (((domains 28).pencil ((table 28).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes55 0 8 (fun x => (maps 28).get i (Normalizers.Source55.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 28).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 28).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 28).length = (((List.finRange (maps 28).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 28).length,
    ((domains 28).pencil ((table 28).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes55 0 8 (fun x => (maps 28).get i (Normalizers.Source55.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source55.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 28) link55 (templates 28).family hole 0 8
    Normalizers.Source55.normalizer00 Normalizers.Source55.record00.hole_fixed Normalizers.Source55.record00.center_image Normalizers.Source55.record00.star_image
    (maps 28) (maps_complete 28) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 28) (table 28)
    RawClass9.CatalogCodes.codes55 link55 RawClass9.CatalogCodes.checked55
    0 8 Normalizers.Source55.normalizer00 (maps 28) pick00 rows00

def pick01 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes55 1 6 (fun x => (maps 35).get i (Normalizers.Source55.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 35).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes55 1 6 (fun x => (maps 35).get i (Normalizers.Source55.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source55.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link55 (templates 35).family hole 1 6
    Normalizers.Source55.normalizer01 Normalizers.Source55.record01.hole_fixed Normalizers.Source55.record01.center_image Normalizers.Source55.record01.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes55 link55 RawClass9.CatalogCodes.checked55
    1 6 Normalizers.Source55.normalizer01 (maps 35) pick01 rows01

theorem complete02 : SourceComplete domains Normalizers.Source55.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source55Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source55.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source55Center03Q8.complete e he hc hs

def pick04 : Fin (maps 28).length → (table 28).Index := ![⟨⟨0,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨37,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨27,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 28).length) : Bool :=
  decide (((domains 28).pencil ((table 28).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes55 4 8 (fun x => (maps 28).get i (Normalizers.Source55.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 28).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 28).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 28).length = (((List.finRange (maps 28).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 28).length,
    ((domains 28).pencil ((table 28).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes55 4 8 (fun x => (maps 28).get i (Normalizers.Source55.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source55.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 28) link55 (templates 28).family hole 4 8
    Normalizers.Source55.normalizer04 Normalizers.Source55.record04.hole_fixed Normalizers.Source55.record04.center_image Normalizers.Source55.record04.star_image
    (maps 28) (maps_complete 28) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 28) (table 28)
    RawClass9.CatalogCodes.codes55 link55 RawClass9.CatalogCodes.checked55
    4 8 Normalizers.Source55.normalizer04 (maps 28) pick04 rows04

theorem complete05 : SourceComplete domains Normalizers.Source55.record05 := by
  intro _ e he hc hs
  exact RawClass9.Source55Center05Q8.complete e he hc hs

def pick06 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩]
def rowCheck06 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick06 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes55 6 6 (fun x => (maps 35).get i (Normalizers.Source55.normalizer06 x))).toFinset)

theorem chunk06_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck06) = true := by decide +kernel
theorem all06 : ((List.finRange (maps 35).length).all rowCheck06) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk06_0
theorem rows06 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick06 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes55 6 6 (fun x => (maps 35).get i (Normalizers.Source55.normalizer06 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all06) i (by simp))

theorem complete06 : SourceComplete domains Normalizers.Source55.record06 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link55 (templates 35).family hole 6 6
    Normalizers.Source55.normalizer06 Normalizers.Source55.record06.hole_fixed Normalizers.Source55.record06.center_image Normalizers.Source55.record06.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes55 link55 RawClass9.CatalogCodes.checked55
    6 6 Normalizers.Source55.normalizer06 (maps 35) pick06 rows06

theorem complete07 : SourceComplete domains Normalizers.Source55.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source55Center07Q8.complete e he hc hs

def pick08 : Fin (maps 54).length → (table 54).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 54).length) : Bool :=
  decide (((domains 54).pencil ((table 54).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes55 8 8 (fun x => (maps 54).get i (Normalizers.Source55.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 54).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 54).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 54).length = (((List.finRange (maps 54).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 54).length,
    ((domains 54).pencil ((table 54).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes55 8 8 (fun x => (maps 54).get i (Normalizers.Source55.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source55.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 54) link55 (templates 54).family hole 8 8
    Normalizers.Source55.normalizer08 Normalizers.Source55.record08.hole_fixed Normalizers.Source55.record08.center_image Normalizers.Source55.record08.star_image
    (maps 54) (maps_complete 54) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 54) (table 54)
    RawClass9.CatalogCodes.codes55 link55 RawClass9.CatalogCodes.checked55
    8 8 Normalizers.Source55.normalizer08 (maps 54) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source55.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source55Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source55.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source55Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source55.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source55Center11Q6.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source55.entries, SourceComplete domains r := by
  simp only [Normalizers.Source55.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source55
