import C13Enumeration.Canonical.Normalizers.Source08
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source08
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 13).length → (table 13).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 13).length) : Bool :=
  decide (((domains 13).pencil ((table 13).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes08 0 0 (fun x => (maps 13).get i (Normalizers.Source08.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 13).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 13).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 13).length = (((List.finRange (maps 13).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 13).length,
    ((domains 13).pencil ((table 13).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes08 0 0 (fun x => (maps 13).get i (Normalizers.Source08.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source08.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 13) link08 (templates 13).family hole 0 0
    Normalizers.Source08.normalizer00 Normalizers.Source08.record00.hole_fixed Normalizers.Source08.record00.center_image Normalizers.Source08.record00.star_image
    (maps 13) (maps_complete 13) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 13) (table 13)
    RawClass9.CatalogCodes.codes08 link08 RawClass9.CatalogCodes.checked08
    0 0 Normalizers.Source08.normalizer00 (maps 13) pick00 rows00

def pick01 : Fin (maps 9).length → (table 9).Index := ![⟨⟨0,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨12,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨12,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 9).length) : Bool :=
  decide (((domains 9).pencil ((table 9).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes08 1 2 (fun x => (maps 9).get i (Normalizers.Source08.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 9).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 9).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 9).length = (((List.finRange (maps 9).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 9).length,
    ((domains 9).pencil ((table 9).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes08 1 2 (fun x => (maps 9).get i (Normalizers.Source08.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source08.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 9) link08 (templates 9).family hole 1 2
    Normalizers.Source08.normalizer01 Normalizers.Source08.record01.hole_fixed Normalizers.Source08.record01.center_image Normalizers.Source08.record01.star_image
    (maps 9) (maps_complete 9) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 9) (table 9)
    RawClass9.CatalogCodes.codes08 link08 RawClass9.CatalogCodes.checked08
    1 2 Normalizers.Source08.normalizer01 (maps 9) pick01 rows01

theorem complete02 : SourceComplete domains Normalizers.Source08.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source08Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source08.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source08Center03Q8.complete e he hc hs

def pick04 : Fin (maps 14).length → (table 14).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 14).length) : Bool :=
  decide (((domains 14).pencil ((table 14).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes08 4 4 (fun x => (maps 14).get i (Normalizers.Source08.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 14).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 14).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 14).length = (((List.finRange (maps 14).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 14).length,
    ((domains 14).pencil ((table 14).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes08 4 4 (fun x => (maps 14).get i (Normalizers.Source08.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source08.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 14) link08 (templates 14).family hole 4 4
    Normalizers.Source08.normalizer04 Normalizers.Source08.record04.hole_fixed Normalizers.Source08.record04.center_image Normalizers.Source08.record04.star_image
    (maps 14) (maps_complete 14) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 14) (table 14)
    RawClass9.CatalogCodes.codes08 link08 RawClass9.CatalogCodes.checked08
    4 4 Normalizers.Source08.normalizer04 (maps 14) pick04 rows04

def pick05 : Fin (maps 15).length → (table 15).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 15).length) : Bool :=
  decide (((domains 15).pencil ((table 15).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes08 5 5 (fun x => (maps 15).get i (Normalizers.Source08.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 15).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 15).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 15).length = (((List.finRange (maps 15).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 15).length,
    ((domains 15).pencil ((table 15).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes08 5 5 (fun x => (maps 15).get i (Normalizers.Source08.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source08.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 15) link08 (templates 15).family hole 5 5
    Normalizers.Source08.normalizer05 Normalizers.Source08.record05.hole_fixed Normalizers.Source08.record05.center_image Normalizers.Source08.record05.star_image
    (maps 15) (maps_complete 15) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 15) (table 15)
    RawClass9.CatalogCodes.codes08 link08 RawClass9.CatalogCodes.checked08
    5 5 Normalizers.Source08.normalizer05 (maps 15) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source08.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source08Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source08.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source08Center07Q8.complete e he hc hs

def pick08 : Fin (maps 8).length → (table 8).Index := ![⟨⟨0,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 8).length) : Bool :=
  decide (((domains 8).pencil ((table 8).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes08 8 6 (fun x => (maps 8).get i (Normalizers.Source08.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 8).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 8).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 8).length = (((List.finRange (maps 8).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 8).length,
    ((domains 8).pencil ((table 8).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes08 8 6 (fun x => (maps 8).get i (Normalizers.Source08.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source08.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 8) link08 (templates 8).family hole 8 6
    Normalizers.Source08.normalizer08 Normalizers.Source08.record08.hole_fixed Normalizers.Source08.record08.center_image Normalizers.Source08.record08.star_image
    (maps 8) (maps_complete 8) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 8) (table 8)
    RawClass9.CatalogCodes.codes08 link08 RawClass9.CatalogCodes.checked08
    8 6 Normalizers.Source08.normalizer08 (maps 8) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source08.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source08Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source08.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source08Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source08.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source08Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source08.entries, SourceComplete domains r := by
  simp only [Normalizers.Source08.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source08
