import C13Enumeration.Canonical.Normalizers.Source31
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source31
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes31 0 2 (fun x => (maps 19).get i (Normalizers.Source31.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 19).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes31 0 2 (fun x => (maps 19).get i (Normalizers.Source31.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source31.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link31 (templates 19).family hole 0 2
    Normalizers.Source31.normalizer00 Normalizers.Source31.record00.hole_fixed Normalizers.Source31.record00.center_image Normalizers.Source31.record00.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes31 link31 RawClass9.CatalogCodes.checked31
    0 2 Normalizers.Source31.normalizer00 (maps 19) pick00 rows00

def pick01 : Fin (maps 10).length → (table 10).Index := ![⟨⟨0,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 10).length) : Bool :=
  decide (((domains 10).pencil ((table 10).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes31 1 2 (fun x => (maps 10).get i (Normalizers.Source31.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 10).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 10).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 10).length = (((List.finRange (maps 10).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 10).length,
    ((domains 10).pencil ((table 10).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes31 1 2 (fun x => (maps 10).get i (Normalizers.Source31.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source31.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 10) link31 (templates 10).family hole 1 2
    Normalizers.Source31.normalizer01 Normalizers.Source31.record01.hole_fixed Normalizers.Source31.record01.center_image Normalizers.Source31.record01.star_image
    (maps 10) (maps_complete 10) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 10) (table 10)
    RawClass9.CatalogCodes.codes31 link31 RawClass9.CatalogCodes.checked31
    1 2 Normalizers.Source31.normalizer01 (maps 10) pick01 rows01

theorem complete02 : SourceComplete domains Normalizers.Source31.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source31Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source31.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source31Center03Q8.complete e he hc hs

def pick04 : Fin (maps 14).length → (table 14).Index := ![⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 14).length) : Bool :=
  decide (((domains 14).pencil ((table 14).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes31 4 4 (fun x => (maps 14).get i (Normalizers.Source31.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 14).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 14).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 14).length = (((List.finRange (maps 14).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 14).length,
    ((domains 14).pencil ((table 14).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes31 4 4 (fun x => (maps 14).get i (Normalizers.Source31.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source31.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 14) link31 (templates 14).family hole 4 4
    Normalizers.Source31.normalizer04 Normalizers.Source31.record04.hole_fixed Normalizers.Source31.record04.center_image Normalizers.Source31.record04.star_image
    (maps 14) (maps_complete 14) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 14) (table 14)
    RawClass9.CatalogCodes.codes31 link31 RawClass9.CatalogCodes.checked31
    4 4 Normalizers.Source31.normalizer04 (maps 14) pick04 rows04

def pick05 : Fin (maps 15).length → (table 15).Index := ![⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 15).length) : Bool :=
  decide (((domains 15).pencil ((table 15).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes31 5 5 (fun x => (maps 15).get i (Normalizers.Source31.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 15).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 15).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 15).length = (((List.finRange (maps 15).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 15).length,
    ((domains 15).pencil ((table 15).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes31 5 5 (fun x => (maps 15).get i (Normalizers.Source31.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source31.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 15) link31 (templates 15).family hole 5 5
    Normalizers.Source31.normalizer05 Normalizers.Source31.record05.hole_fixed Normalizers.Source31.record05.center_image Normalizers.Source31.record05.star_image
    (maps 15) (maps_complete 15) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 15) (table 15)
    RawClass9.CatalogCodes.codes31 link31 RawClass9.CatalogCodes.checked31
    5 5 Normalizers.Source31.normalizer05 (maps 15) pick05 rows05

def pick06 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩]
def rowCheck06 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick06 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes31 6 6 (fun x => (maps 35).get i (Normalizers.Source31.normalizer06 x))).toFinset)

theorem chunk06_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck06) = true := by decide +kernel
theorem all06 : ((List.finRange (maps 35).length).all rowCheck06) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk06_0
theorem rows06 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick06 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes31 6 6 (fun x => (maps 35).get i (Normalizers.Source31.normalizer06 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all06) i (by simp))

theorem complete06 : SourceComplete domains Normalizers.Source31.record06 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link31 (templates 35).family hole 6 6
    Normalizers.Source31.normalizer06 Normalizers.Source31.record06.hole_fixed Normalizers.Source31.record06.center_image Normalizers.Source31.record06.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes31 link31 RawClass9.CatalogCodes.checked31
    6 6 Normalizers.Source31.normalizer06 (maps 35) pick06 rows06

theorem complete07 : SourceComplete domains Normalizers.Source31.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source31Center07Q8.complete e he hc hs

def pick08 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes31 8 6 (fun x => (maps 35).get i (Normalizers.Source31.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 35).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes31 8 6 (fun x => (maps 35).get i (Normalizers.Source31.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source31.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link31 (templates 35).family hole 8 6
    Normalizers.Source31.normalizer08 Normalizers.Source31.record08.hole_fixed Normalizers.Source31.record08.center_image Normalizers.Source31.record08.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes31 link31 RawClass9.CatalogCodes.checked31
    8 6 Normalizers.Source31.normalizer08 (maps 35) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source31.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source31Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source31.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source31Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source31.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source31Center11Q6.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source31.entries, SourceComplete domains r := by
  simp only [Normalizers.Source31.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source31
