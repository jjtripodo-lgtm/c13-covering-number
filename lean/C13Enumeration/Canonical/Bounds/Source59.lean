import C13Enumeration.Canonical.Normalizers.Source59
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source59
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 34).length → (table 34).Index := ![⟨⟨0,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 34).length) : Bool :=
  decide (((domains 34).pencil ((table 34).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes59 0 8 (fun x => (maps 34).get i (Normalizers.Source59.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 34).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 34).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 34).length = (((List.finRange (maps 34).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 34).length,
    ((domains 34).pencil ((table 34).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes59 0 8 (fun x => (maps 34).get i (Normalizers.Source59.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source59.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 34) link59 (templates 34).family hole 0 8
    Normalizers.Source59.normalizer00 Normalizers.Source59.record00.hole_fixed Normalizers.Source59.record00.center_image Normalizers.Source59.record00.star_image
    (maps 34) (maps_complete 34) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 34) (table 34)
    RawClass9.CatalogCodes.codes59 link59 RawClass9.CatalogCodes.checked59
    0 8 Normalizers.Source59.normalizer00 (maps 34) pick00 rows00

def pick01 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes59 1 6 (fun x => (maps 35).get i (Normalizers.Source59.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 35).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes59 1 6 (fun x => (maps 35).get i (Normalizers.Source59.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source59.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link59 (templates 35).family hole 1 6
    Normalizers.Source59.normalizer01 Normalizers.Source59.record01.hole_fixed Normalizers.Source59.record01.center_image Normalizers.Source59.record01.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes59 link59 RawClass9.CatalogCodes.checked59
    1 6 Normalizers.Source59.normalizer01 (maps 35) pick01 rows01

theorem complete02 : SourceComplete domains Normalizers.Source59.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source59Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source59.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source59Center03Q8.complete e he hc hs

def pick04 : Fin (maps 8).length → (table 8).Index := ![⟨⟨0,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 8).length) : Bool :=
  decide (((domains 8).pencil ((table 8).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes59 4 6 (fun x => (maps 8).get i (Normalizers.Source59.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 8).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 8).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 8).length = (((List.finRange (maps 8).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 8).length,
    ((domains 8).pencil ((table 8).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes59 4 6 (fun x => (maps 8).get i (Normalizers.Source59.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source59.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 8) link59 (templates 8).family hole 4 6
    Normalizers.Source59.normalizer04 Normalizers.Source59.record04.hole_fixed Normalizers.Source59.record04.center_image Normalizers.Source59.record04.star_image
    (maps 8) (maps_complete 8) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 8) (table 8)
    RawClass9.CatalogCodes.codes59 link59 RawClass9.CatalogCodes.checked59
    4 6 Normalizers.Source59.normalizer04 (maps 8) pick04 rows04

theorem complete05 : SourceComplete domains Normalizers.Source59.record05 := by
  intro _ e he hc hs
  exact RawClass9.Source59Center05Q6.complete e he hc hs

def pick06 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩]
def rowCheck06 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick06 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes59 6 6 (fun x => (maps 35).get i (Normalizers.Source59.normalizer06 x))).toFinset)

theorem chunk06_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck06) = true := by decide +kernel
theorem all06 : ((List.finRange (maps 35).length).all rowCheck06) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk06_0
theorem rows06 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick06 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes59 6 6 (fun x => (maps 35).get i (Normalizers.Source59.normalizer06 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all06) i (by simp))

theorem complete06 : SourceComplete domains Normalizers.Source59.record06 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link59 (templates 35).family hole 6 6
    Normalizers.Source59.normalizer06 Normalizers.Source59.record06.hole_fixed Normalizers.Source59.record06.center_image Normalizers.Source59.record06.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes59 link59 RawClass9.CatalogCodes.checked59
    6 6 Normalizers.Source59.normalizer06 (maps 35) pick06 rows06

theorem complete07 : SourceComplete domains Normalizers.Source59.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source59Center07Q8.complete e he hc hs

def pick08 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨37,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes59 8 6 (fun x => (maps 35).get i (Normalizers.Source59.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 35).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes59 8 6 (fun x => (maps 35).get i (Normalizers.Source59.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source59.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link59 (templates 35).family hole 8 6
    Normalizers.Source59.normalizer08 Normalizers.Source59.record08.hole_fixed Normalizers.Source59.record08.center_image Normalizers.Source59.record08.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes59 link59 RawClass9.CatalogCodes.checked59
    8 6 Normalizers.Source59.normalizer08 (maps 35) pick08 rows08

def pick09 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩]
def rowCheck09 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick09 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes59 9 6 (fun x => (maps 35).get i (Normalizers.Source59.normalizer09 x))).toFinset)

theorem chunk09_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck09) = true := by decide +kernel
theorem all09 : ((List.finRange (maps 35).length).all rowCheck09) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk09_0
theorem rows09 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick09 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes59 9 6 (fun x => (maps 35).get i (Normalizers.Source59.normalizer09 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all09) i (by simp))

theorem complete09 : SourceComplete domains Normalizers.Source59.record09 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link59 (templates 35).family hole 9 6
    Normalizers.Source59.normalizer09 Normalizers.Source59.record09.hole_fixed Normalizers.Source59.record09.center_image Normalizers.Source59.record09.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes59 link59 RawClass9.CatalogCodes.checked59
    9 6 Normalizers.Source59.normalizer09 (maps 35) pick09 rows09

theorem complete10 : SourceComplete domains Normalizers.Source59.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source59Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source59.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source59Center11Q6.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source59.entries, SourceComplete domains r := by
  simp only [Normalizers.Source59.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source59
