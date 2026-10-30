import C13Enumeration.Canonical.Normalizers.Source54
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source54
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 28).length → (table 28).Index := ![⟨⟨0,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 28).length) : Bool :=
  decide (((domains 28).pencil ((table 28).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes54 0 8 (fun x => (maps 28).get i (Normalizers.Source54.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 28).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 28).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 28).length = (((List.finRange (maps 28).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 28).length,
    ((domains 28).pencil ((table 28).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes54 0 8 (fun x => (maps 28).get i (Normalizers.Source54.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source54.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 28) link54 (templates 28).family hole 0 8
    Normalizers.Source54.normalizer00 Normalizers.Source54.record00.hole_fixed Normalizers.Source54.record00.center_image Normalizers.Source54.record00.star_image
    (maps 28) (maps_complete 28) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 28) (table 28)
    RawClass9.CatalogCodes.codes54 link54 RawClass9.CatalogCodes.checked54
    0 8 Normalizers.Source54.normalizer00 (maps 28) pick00 rows00

def pick01 : Fin (maps 8).length → (table 8).Index := ![⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 8).length) : Bool :=
  decide (((domains 8).pencil ((table 8).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes54 1 6 (fun x => (maps 8).get i (Normalizers.Source54.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 8).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 8).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 8).length = (((List.finRange (maps 8).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 8).length,
    ((domains 8).pencil ((table 8).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes54 1 6 (fun x => (maps 8).get i (Normalizers.Source54.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source54.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 8) link54 (templates 8).family hole 1 6
    Normalizers.Source54.normalizer01 Normalizers.Source54.record01.hole_fixed Normalizers.Source54.record01.center_image Normalizers.Source54.record01.star_image
    (maps 8) (maps_complete 8) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 8) (table 8)
    RawClass9.CatalogCodes.codes54 link54 RawClass9.CatalogCodes.checked54
    1 6 Normalizers.Source54.normalizer01 (maps 8) pick01 rows01

theorem complete02 : SourceComplete domains Normalizers.Source54.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source54Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source54.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source54Center03Q8.complete e he hc hs

def pick04 : Fin (maps 28).length → (table 28).Index := ![⟨⟨0,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 28).length) : Bool :=
  decide (((domains 28).pencil ((table 28).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes54 4 8 (fun x => (maps 28).get i (Normalizers.Source54.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 28).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 28).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 28).length = (((List.finRange (maps 28).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 28).length,
    ((domains 28).pencil ((table 28).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes54 4 8 (fun x => (maps 28).get i (Normalizers.Source54.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source54.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 28) link54 (templates 28).family hole 4 8
    Normalizers.Source54.normalizer04 Normalizers.Source54.record04.hole_fixed Normalizers.Source54.record04.center_image Normalizers.Source54.record04.star_image
    (maps 28) (maps_complete 28) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 28) (table 28)
    RawClass9.CatalogCodes.codes54 link54 RawClass9.CatalogCodes.checked54
    4 8 Normalizers.Source54.normalizer04 (maps 28) pick04 rows04

def pick05 : Fin (maps 8).length → (table 8).Index := ![⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 8).length) : Bool :=
  decide (((domains 8).pencil ((table 8).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes54 5 6 (fun x => (maps 8).get i (Normalizers.Source54.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 8).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 8).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 8).length = (((List.finRange (maps 8).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 8).length,
    ((domains 8).pencil ((table 8).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes54 5 6 (fun x => (maps 8).get i (Normalizers.Source54.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source54.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 8) link54 (templates 8).family hole 5 6
    Normalizers.Source54.normalizer05 Normalizers.Source54.record05.hole_fixed Normalizers.Source54.record05.center_image Normalizers.Source54.record05.star_image
    (maps 8) (maps_complete 8) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 8) (table 8)
    RawClass9.CatalogCodes.codes54 link54 RawClass9.CatalogCodes.checked54
    5 6 Normalizers.Source54.normalizer05 (maps 8) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source54.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source54Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source54.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source54Center07Q8.complete e he hc hs

def pick08 : Fin (maps 53).length → (table 53).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 53).length) : Bool :=
  decide (((domains 53).pencil ((table 53).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes54 8 8 (fun x => (maps 53).get i (Normalizers.Source54.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 53).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 53).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 53).length = (((List.finRange (maps 53).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 53).length,
    ((domains 53).pencil ((table 53).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes54 8 8 (fun x => (maps 53).get i (Normalizers.Source54.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source54.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 53) link54 (templates 53).family hole 8 8
    Normalizers.Source54.normalizer08 Normalizers.Source54.record08.hole_fixed Normalizers.Source54.record08.center_image Normalizers.Source54.record08.star_image
    (maps 53) (maps_complete 53) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 53) (table 53)
    RawClass9.CatalogCodes.codes54 link54 RawClass9.CatalogCodes.checked54
    8 8 Normalizers.Source54.normalizer08 (maps 53) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source54.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source54Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source54.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source54Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source54.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source54Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source54.entries, SourceComplete domains r := by
  simp only [Normalizers.Source54.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source54
