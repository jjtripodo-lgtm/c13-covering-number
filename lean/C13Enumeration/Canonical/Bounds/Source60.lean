import C13Enumeration.Canonical.Normalizers.Source60
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source60
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 34).length → (table 34).Index := ![⟨⟨0,by decide +kernel⟩,⟨37,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 34).length) : Bool :=
  decide (((domains 34).pencil ((table 34).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes60 0 8 (fun x => (maps 34).get i (Normalizers.Source60.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 34).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 34).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 34).length = (((List.finRange (maps 34).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 34).length,
    ((domains 34).pencil ((table 34).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes60 0 8 (fun x => (maps 34).get i (Normalizers.Source60.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source60.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 34) link60 (templates 34).family hole 0 8
    Normalizers.Source60.normalizer00 Normalizers.Source60.record00.hole_fixed Normalizers.Source60.record00.center_image Normalizers.Source60.record00.star_image
    (maps 34) (maps_complete 34) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 34) (table 34)
    RawClass9.CatalogCodes.codes60 link60 RawClass9.CatalogCodes.checked60
    0 8 Normalizers.Source60.normalizer00 (maps 34) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source60.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source60Center01Q8.complete e he hc hs

def pick02 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨12,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes60 2 2 (fun x => (maps 19).get i (Normalizers.Source60.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 19).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes60 2 2 (fun x => (maps 19).get i (Normalizers.Source60.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source60.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link60 (templates 19).family hole 2 2
    Normalizers.Source60.normalizer02 Normalizers.Source60.record02.hole_fixed Normalizers.Source60.record02.center_image Normalizers.Source60.record02.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes60 link60 RawClass9.CatalogCodes.checked60
    2 2 Normalizers.Source60.normalizer02 (maps 19) pick02 rows02

theorem complete03 : SourceComplete domains Normalizers.Source60.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source60Center03Q8.complete e he hc hs

def pick04 : Fin (maps 57).length → (table 57).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 57).length) : Bool :=
  decide (((domains 57).pencil ((table 57).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes60 4 4 (fun x => (maps 57).get i (Normalizers.Source60.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 57).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 57).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 57).length = (((List.finRange (maps 57).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 57).length,
    ((domains 57).pencil ((table 57).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes60 4 4 (fun x => (maps 57).get i (Normalizers.Source60.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source60.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 57) link60 (templates 57).family hole 4 4
    Normalizers.Source60.normalizer04 Normalizers.Source60.record04.hole_fixed Normalizers.Source60.record04.center_image Normalizers.Source60.record04.star_image
    (maps 57) (maps_complete 57) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 57) (table 57)
    RawClass9.CatalogCodes.codes60 link60 RawClass9.CatalogCodes.checked60
    4 4 Normalizers.Source60.normalizer04 (maps 57) pick04 rows04

theorem complete05 : SourceComplete domains Normalizers.Source60.record05 := by
  intro _ e he hc hs
  exact RawClass9.Source60Center05Q6.complete e he hc hs

theorem complete06 : SourceComplete domains Normalizers.Source60.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source60Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source60.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source60Center07Q8.complete e he hc hs

def pick08 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes60 8 2 (fun x => (maps 19).get i (Normalizers.Source60.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 19).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes60 8 2 (fun x => (maps 19).get i (Normalizers.Source60.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source60.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link60 (templates 19).family hole 8 2
    Normalizers.Source60.normalizer08 Normalizers.Source60.record08.hole_fixed Normalizers.Source60.record08.center_image Normalizers.Source60.record08.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes60 link60 RawClass9.CatalogCodes.checked60
    8 2 Normalizers.Source60.normalizer08 (maps 19) pick08 rows08

def pick09 : Fin (maps 35).length → (table 35).Index := ![⟨⟨0,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩]
def rowCheck09 (i : Fin (maps 35).length) : Bool :=
  decide (((domains 35).pencil ((table 35).row (pick09 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes60 9 6 (fun x => (maps 35).get i (Normalizers.Source60.normalizer09 x))).toFinset)

theorem chunk09_0 : ((((List.finRange (maps 35).length).drop 0).take 16).all rowCheck09) = true := by decide +kernel
theorem all09 : ((List.finRange (maps 35).length).all rowCheck09) = true := by
  have hsplit : List.finRange (maps 35).length = (((List.finRange (maps 35).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk09_0
theorem rows09 : ∀ i : Fin (maps 35).length,
    ((domains 35).pencil ((table 35).row (pick09 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes60 9 6 (fun x => (maps 35).get i (Normalizers.Source60.normalizer09 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all09) i (by simp))

theorem complete09 : SourceComplete domains Normalizers.Source60.record09 := by
  intro _ e he hc hs
  apply source_center_represented (domains 35) link60 (templates 35).family hole 9 6
    Normalizers.Source60.normalizer09 Normalizers.Source60.record09.hole_fixed Normalizers.Source60.record09.center_image Normalizers.Source60.record09.star_image
    (maps 35) (maps_complete 35) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 35) (table 35)
    RawClass9.CatalogCodes.codes60 link60 RawClass9.CatalogCodes.checked60
    9 6 Normalizers.Source60.normalizer09 (maps 35) pick09 rows09

theorem complete10 : SourceComplete domains Normalizers.Source60.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source60Center10Q6.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source60.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source60Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source60.entries, SourceComplete domains r := by
  simp only [Normalizers.Source60.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source60
