import C13Enumeration.Canonical.Normalizers.Source38
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source38
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨40,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes38 0 2 (fun x => (maps 19).get i (Normalizers.Source38.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 19).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes38 0 2 (fun x => (maps 19).get i (Normalizers.Source38.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source38.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link38 (templates 19).family hole 0 2
    Normalizers.Source38.normalizer00 Normalizers.Source38.record00.hole_fixed Normalizers.Source38.record00.center_image Normalizers.Source38.record00.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes38 link38 RawClass9.CatalogCodes.checked38
    0 2 Normalizers.Source38.normalizer00 (maps 19) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source38.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source38Center01Q8.complete e he hc hs

theorem complete02 : SourceComplete domains Normalizers.Source38.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source38Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source38.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source38Center03Q8.complete e he hc hs

def pick04 : Fin (maps 14).length → (table 14).Index := ![⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 14).length) : Bool :=
  decide (((domains 14).pencil ((table 14).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes38 4 4 (fun x => (maps 14).get i (Normalizers.Source38.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 14).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 14).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 14).length = (((List.finRange (maps 14).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 14).length,
    ((domains 14).pencil ((table 14).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes38 4 4 (fun x => (maps 14).get i (Normalizers.Source38.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source38.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 14) link38 (templates 14).family hole 4 4
    Normalizers.Source38.normalizer04 Normalizers.Source38.record04.hole_fixed Normalizers.Source38.record04.center_image Normalizers.Source38.record04.star_image
    (maps 14) (maps_complete 14) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 14) (table 14)
    RawClass9.CatalogCodes.codes38 link38 RawClass9.CatalogCodes.checked38
    4 4 Normalizers.Source38.normalizer04 (maps 14) pick04 rows04

def pick05 : Fin (maps 41).length → (table 41).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 41).length) : Bool :=
  decide (((domains 41).pencil ((table 41).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes38 5 5 (fun x => (maps 41).get i (Normalizers.Source38.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 41).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 41).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 41).length = (((List.finRange (maps 41).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 41).length,
    ((domains 41).pencil ((table 41).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes38 5 5 (fun x => (maps 41).get i (Normalizers.Source38.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source38.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 41) link38 (templates 41).family hole 5 5
    Normalizers.Source38.normalizer05 Normalizers.Source38.record05.hole_fixed Normalizers.Source38.record05.center_image Normalizers.Source38.record05.star_image
    (maps 41) (maps_complete 41) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 41) (table 41)
    RawClass9.CatalogCodes.codes38 link38 RawClass9.CatalogCodes.checked38
    5 5 Normalizers.Source38.normalizer05 (maps 41) pick05 rows05

def pick06 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩]
def rowCheck06 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick06 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes38 6 4 (fun x => (maps 17).get i (Normalizers.Source38.normalizer06 x))).toFinset)

theorem chunk06_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck06) = true := by decide +kernel
theorem all06 : ((List.finRange (maps 17).length).all rowCheck06) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk06_0
theorem rows06 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick06 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes38 6 4 (fun x => (maps 17).get i (Normalizers.Source38.normalizer06 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all06) i (by simp))

theorem complete06 : SourceComplete domains Normalizers.Source38.record06 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link38 (templates 17).family hole 6 4
    Normalizers.Source38.normalizer06 Normalizers.Source38.record06.hole_fixed Normalizers.Source38.record06.center_image Normalizers.Source38.record06.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes38 link38 RawClass9.CatalogCodes.checked38
    6 4 Normalizers.Source38.normalizer06 (maps 17) pick06 rows06

theorem complete07 : SourceComplete domains Normalizers.Source38.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source38Center07Q8.complete e he hc hs

def pick08 : Fin (maps 18).length → (table 18).Index := ![⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 18).length) : Bool :=
  decide (((domains 18).pencil ((table 18).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes38 8 2 (fun x => (maps 18).get i (Normalizers.Source38.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 18).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 18).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 18).length = (((List.finRange (maps 18).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 18).length,
    ((domains 18).pencil ((table 18).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes38 8 2 (fun x => (maps 18).get i (Normalizers.Source38.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source38.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 18) link38 (templates 18).family hole 8 2
    Normalizers.Source38.normalizer08 Normalizers.Source38.record08.hole_fixed Normalizers.Source38.record08.center_image Normalizers.Source38.record08.star_image
    (maps 18) (maps_complete 18) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 18) (table 18)
    RawClass9.CatalogCodes.codes38 link38 RawClass9.CatalogCodes.checked38
    8 2 Normalizers.Source38.normalizer08 (maps 18) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source38.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source38Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source38.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source38Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source38.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source38Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source38.entries, SourceComplete domains r := by
  simp only [Normalizers.Source38.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source38
