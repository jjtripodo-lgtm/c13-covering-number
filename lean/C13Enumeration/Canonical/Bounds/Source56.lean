import C13Enumeration.Canonical.Normalizers.Source56
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source56
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 55).length → (table 55).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 55).length) : Bool :=
  decide (((domains 55).pencil ((table 55).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes56 0 0 (fun x => (maps 55).get i (Normalizers.Source56.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 55).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 55).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 55).length = (((List.finRange (maps 55).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 55).length,
    ((domains 55).pencil ((table 55).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes56 0 0 (fun x => (maps 55).get i (Normalizers.Source56.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source56.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 55) link56 (templates 55).family hole 0 0
    Normalizers.Source56.normalizer00 Normalizers.Source56.record00.hole_fixed Normalizers.Source56.record00.center_image Normalizers.Source56.record00.star_image
    (maps 55) (maps_complete 55) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 55) (table 55)
    RawClass9.CatalogCodes.codes56 link56 RawClass9.CatalogCodes.checked56
    0 0 Normalizers.Source56.normalizer00 (maps 55) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source56.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source56Center01Q8.complete e he hc hs

theorem complete02 : SourceComplete domains Normalizers.Source56.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source56Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source56.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source56Center03Q8.complete e he hc hs

def pick04 : Fin (maps 8).length → (table 8).Index := ![⟨⟨0,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 8).length) : Bool :=
  decide (((domains 8).pencil ((table 8).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes56 4 6 (fun x => (maps 8).get i (Normalizers.Source56.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 8).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 8).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 8).length = (((List.finRange (maps 8).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 8).length,
    ((domains 8).pencil ((table 8).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes56 4 6 (fun x => (maps 8).get i (Normalizers.Source56.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source56.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 8) link56 (templates 8).family hole 4 6
    Normalizers.Source56.normalizer04 Normalizers.Source56.record04.hole_fixed Normalizers.Source56.record04.center_image Normalizers.Source56.record04.star_image
    (maps 8) (maps_complete 8) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 8) (table 8)
    RawClass9.CatalogCodes.codes56 link56 RawClass9.CatalogCodes.checked56
    4 6 Normalizers.Source56.normalizer04 (maps 8) pick04 rows04

theorem complete05 : SourceComplete domains Normalizers.Source56.record05 := by
  intro _ e he hc hs
  exact RawClass9.Source56Center05Q6.complete e he hc hs

def pick06 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩]
def rowCheck06 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick06 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes56 6 2 (fun x => (maps 19).get i (Normalizers.Source56.normalizer06 x))).toFinset)

theorem chunk06_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck06) = true := by decide +kernel
theorem all06 : ((List.finRange (maps 19).length).all rowCheck06) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk06_0
theorem rows06 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick06 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes56 6 2 (fun x => (maps 19).get i (Normalizers.Source56.normalizer06 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all06) i (by simp))

theorem complete06 : SourceComplete domains Normalizers.Source56.record06 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link56 (templates 19).family hole 6 2
    Normalizers.Source56.normalizer06 Normalizers.Source56.record06.hole_fixed Normalizers.Source56.record06.center_image Normalizers.Source56.record06.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes56 link56 RawClass9.CatalogCodes.checked56
    6 2 Normalizers.Source56.normalizer06 (maps 19) pick06 rows06

theorem complete07 : SourceComplete domains Normalizers.Source56.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source56Center07Q8.complete e he hc hs

def pick08 : Fin (maps 8).length → (table 8).Index := ![⟨⟨0,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 8).length) : Bool :=
  decide (((domains 8).pencil ((table 8).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes56 8 6 (fun x => (maps 8).get i (Normalizers.Source56.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 8).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 8).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 8).length = (((List.finRange (maps 8).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 8).length,
    ((domains 8).pencil ((table 8).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes56 8 6 (fun x => (maps 8).get i (Normalizers.Source56.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source56.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 8) link56 (templates 8).family hole 8 6
    Normalizers.Source56.normalizer08 Normalizers.Source56.record08.hole_fixed Normalizers.Source56.record08.center_image Normalizers.Source56.record08.star_image
    (maps 8) (maps_complete 8) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 8) (table 8)
    RawClass9.CatalogCodes.codes56 link56 RawClass9.CatalogCodes.checked56
    8 6 Normalizers.Source56.normalizer08 (maps 8) pick08 rows08

def pick09 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩]
def rowCheck09 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick09 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes56 9 2 (fun x => (maps 19).get i (Normalizers.Source56.normalizer09 x))).toFinset)

theorem chunk09_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck09) = true := by decide +kernel
theorem all09 : ((List.finRange (maps 19).length).all rowCheck09) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk09_0
theorem rows09 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick09 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes56 9 2 (fun x => (maps 19).get i (Normalizers.Source56.normalizer09 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all09) i (by simp))

theorem complete09 : SourceComplete domains Normalizers.Source56.record09 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link56 (templates 19).family hole 9 2
    Normalizers.Source56.normalizer09 Normalizers.Source56.record09.hole_fixed Normalizers.Source56.record09.center_image Normalizers.Source56.record09.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes56 link56 RawClass9.CatalogCodes.checked56
    9 2 Normalizers.Source56.normalizer09 (maps 19) pick09 rows09

theorem complete10 : SourceComplete domains Normalizers.Source56.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source56Center10Q6.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source56.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source56Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source56.entries, SourceComplete domains r := by
  simp only [Normalizers.Source56.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source56
