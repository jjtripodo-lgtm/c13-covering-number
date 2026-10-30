import C13Enumeration.Canonical.Normalizers.Source30
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source30
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes30 0 2 (fun x => (maps 19).get i (Normalizers.Source30.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 19).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes30 0 2 (fun x => (maps 19).get i (Normalizers.Source30.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source30.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link30 (templates 19).family hole 0 2
    Normalizers.Source30.normalizer00 Normalizers.Source30.record00.hole_fixed Normalizers.Source30.record00.center_image Normalizers.Source30.record00.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes30 link30 RawClass9.CatalogCodes.checked30
    0 2 Normalizers.Source30.normalizer00 (maps 19) pick00 rows00

def pick01 : Fin (maps 8).length → (table 8).Index := ![⟨⟨0,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 8).length) : Bool :=
  decide (((domains 8).pencil ((table 8).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes30 1 6 (fun x => (maps 8).get i (Normalizers.Source30.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 8).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 8).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 8).length = (((List.finRange (maps 8).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 8).length,
    ((domains 8).pencil ((table 8).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes30 1 6 (fun x => (maps 8).get i (Normalizers.Source30.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source30.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 8) link30 (templates 8).family hole 1 6
    Normalizers.Source30.normalizer01 Normalizers.Source30.record01.hole_fixed Normalizers.Source30.record01.center_image Normalizers.Source30.record01.star_image
    (maps 8) (maps_complete 8) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 8) (table 8)
    RawClass9.CatalogCodes.codes30 link30 RawClass9.CatalogCodes.checked30
    1 6 Normalizers.Source30.normalizer01 (maps 8) pick01 rows01

theorem complete02 : SourceComplete domains Normalizers.Source30.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source30Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source30.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source30Center03Q8.complete e he hc hs

def pick04 : Fin (maps 14).length → (table 14).Index := ![⟨⟨0,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 14).length) : Bool :=
  decide (((domains 14).pencil ((table 14).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes30 4 4 (fun x => (maps 14).get i (Normalizers.Source30.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 14).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 14).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 14).length = (((List.finRange (maps 14).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 14).length,
    ((domains 14).pencil ((table 14).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes30 4 4 (fun x => (maps 14).get i (Normalizers.Source30.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source30.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 14) link30 (templates 14).family hole 4 4
    Normalizers.Source30.normalizer04 Normalizers.Source30.record04.hole_fixed Normalizers.Source30.record04.center_image Normalizers.Source30.record04.star_image
    (maps 14) (maps_complete 14) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 14) (table 14)
    RawClass9.CatalogCodes.codes30 link30 RawClass9.CatalogCodes.checked30
    4 4 Normalizers.Source30.normalizer04 (maps 14) pick04 rows04

def pick05 : Fin (maps 33).length → (table 33).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 33).length) : Bool :=
  decide (((domains 33).pencil ((table 33).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes30 5 5 (fun x => (maps 33).get i (Normalizers.Source30.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 33).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 33).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 33).length = (((List.finRange (maps 33).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 33).length,
    ((domains 33).pencil ((table 33).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes30 5 5 (fun x => (maps 33).get i (Normalizers.Source30.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source30.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 33) link30 (templates 33).family hole 5 5
    Normalizers.Source30.normalizer05 Normalizers.Source30.record05.hole_fixed Normalizers.Source30.record05.center_image Normalizers.Source30.record05.star_image
    (maps 33) (maps_complete 33) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 33) (table 33)
    RawClass9.CatalogCodes.codes30 link30 RawClass9.CatalogCodes.checked30
    5 5 Normalizers.Source30.normalizer05 (maps 33) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source30.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source30Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source30.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source30Center07Q8.complete e he hc hs

def pick08 : Fin (maps 34).length → (table 34).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 34).length) : Bool :=
  decide (((domains 34).pencil ((table 34).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes30 8 8 (fun x => (maps 34).get i (Normalizers.Source30.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 34).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 34).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 34).length = (((List.finRange (maps 34).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 34).length,
    ((domains 34).pencil ((table 34).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes30 8 8 (fun x => (maps 34).get i (Normalizers.Source30.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source30.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 34) link30 (templates 34).family hole 8 8
    Normalizers.Source30.normalizer08 Normalizers.Source30.record08.hole_fixed Normalizers.Source30.record08.center_image Normalizers.Source30.record08.star_image
    (maps 34) (maps_complete 34) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 34) (table 34)
    RawClass9.CatalogCodes.codes30 link30 RawClass9.CatalogCodes.checked30
    8 8 Normalizers.Source30.normalizer08 (maps 34) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source30.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source30Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source30.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source30Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source30.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source30Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source30.entries, SourceComplete domains r := by
  simp only [Normalizers.Source30.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source30
