import C13Enumeration.Canonical.Normalizers.Source64
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source64
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem complete00 : SourceComplete domains Normalizers.Source64.record00 := by
  intro _ e he hc hs
  exact RawClass9.Source64Center00Q6.complete e he hc hs

def pick01 : Fin (maps 59).length → (table 59).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 59).length) : Bool :=
  decide (((domains 59).pencil ((table 59).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes64 1 1 (fun x => (maps 59).get i (Normalizers.Source64.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 59).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 59).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 59).length = (((List.finRange (maps 59).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 59).length,
    ((domains 59).pencil ((table 59).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes64 1 1 (fun x => (maps 59).get i (Normalizers.Source64.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source64.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 59) link64 (templates 59).family hole 1 1
    Normalizers.Source64.normalizer01 Normalizers.Source64.record01.hole_fixed Normalizers.Source64.record01.center_image Normalizers.Source64.record01.star_image
    (maps 59) (maps_complete 59) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 59) (table 59)
    RawClass9.CatalogCodes.codes64 link64 RawClass9.CatalogCodes.checked64
    1 1 Normalizers.Source64.normalizer01 (maps 59) pick01 rows01

theorem complete02 : SourceComplete domains Normalizers.Source64.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source64Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source64.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source64Center03Q8.complete e he hc hs

def pick04 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes64 4 2 (fun x => (maps 19).get i (Normalizers.Source64.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 19).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes64 4 2 (fun x => (maps 19).get i (Normalizers.Source64.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source64.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link64 (templates 19).family hole 4 2
    Normalizers.Source64.normalizer04 Normalizers.Source64.record04.hole_fixed Normalizers.Source64.record04.center_image Normalizers.Source64.record04.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes64 link64 RawClass9.CatalogCodes.checked64
    4 2 Normalizers.Source64.normalizer04 (maps 19) pick04 rows04

theorem complete05 : SourceComplete domains Normalizers.Source64.record05 := by
  intro _ e he hc hs
  exact RawClass9.Source64Center05Q6.complete e he hc hs

def pick06 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩]
def rowCheck06 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick06 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes64 6 2 (fun x => (maps 19).get i (Normalizers.Source64.normalizer06 x))).toFinset)

theorem chunk06_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck06) = true := by decide +kernel
theorem all06 : ((List.finRange (maps 19).length).all rowCheck06) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk06_0
theorem rows06 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick06 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes64 6 2 (fun x => (maps 19).get i (Normalizers.Source64.normalizer06 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all06) i (by simp))

theorem complete06 : SourceComplete domains Normalizers.Source64.record06 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link64 (templates 19).family hole 6 2
    Normalizers.Source64.normalizer06 Normalizers.Source64.record06.hole_fixed Normalizers.Source64.record06.center_image Normalizers.Source64.record06.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes64 link64 RawClass9.CatalogCodes.checked64
    6 2 Normalizers.Source64.normalizer06 (maps 19) pick06 rows06

theorem complete07 : SourceComplete domains Normalizers.Source64.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source64Center07Q8.complete e he hc hs

def pick08 : Fin (maps 59).length → (table 59).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 59).length) : Bool :=
  decide (((domains 59).pencil ((table 59).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes64 8 1 (fun x => (maps 59).get i (Normalizers.Source64.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 59).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 59).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 59).length = (((List.finRange (maps 59).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 59).length,
    ((domains 59).pencil ((table 59).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes64 8 1 (fun x => (maps 59).get i (Normalizers.Source64.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source64.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 59) link64 (templates 59).family hole 8 1
    Normalizers.Source64.normalizer08 Normalizers.Source64.record08.hole_fixed Normalizers.Source64.record08.center_image Normalizers.Source64.record08.star_image
    (maps 59) (maps_complete 59) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 59) (table 59)
    RawClass9.CatalogCodes.codes64 link64 RawClass9.CatalogCodes.checked64
    8 1 Normalizers.Source64.normalizer08 (maps 59) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source64.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source64Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source64.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source64Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source64.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source64Center11Q6.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source64.entries, SourceComplete domains r := by
  simp only [Normalizers.Source64.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source64
