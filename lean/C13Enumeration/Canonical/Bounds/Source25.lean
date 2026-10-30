import C13Enumeration.Canonical.Normalizers.Source25
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source25
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes25 0 2 (fun x => (maps 4).get i (Normalizers.Source25.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 4).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes25 0 2 (fun x => (maps 4).get i (Normalizers.Source25.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source25.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link25 (templates 4).family hole 0 2
    Normalizers.Source25.normalizer00 Normalizers.Source25.record00.hole_fixed Normalizers.Source25.record00.center_image Normalizers.Source25.record00.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes25 link25 RawClass9.CatalogCodes.checked25
    0 2 Normalizers.Source25.normalizer00 (maps 4) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source25.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source25Center01Q8.complete e he hc hs

def pick02 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes25 2 2 (fun x => (maps 4).get i (Normalizers.Source25.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 4).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes25 2 2 (fun x => (maps 4).get i (Normalizers.Source25.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source25.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link25 (templates 4).family hole 2 2
    Normalizers.Source25.normalizer02 Normalizers.Source25.record02.hole_fixed Normalizers.Source25.record02.center_image Normalizers.Source25.record02.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes25 link25 RawClass9.CatalogCodes.checked25
    2 2 Normalizers.Source25.normalizer02 (maps 4) pick02 rows02

theorem complete03 : SourceComplete domains Normalizers.Source25.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source25Center03Q8.complete e he hc hs

def pick04 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes25 4 2 (fun x => (maps 4).get i (Normalizers.Source25.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 4).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes25 4 2 (fun x => (maps 4).get i (Normalizers.Source25.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source25.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link25 (templates 4).family hole 4 2
    Normalizers.Source25.normalizer04 Normalizers.Source25.record04.hole_fixed Normalizers.Source25.record04.center_image Normalizers.Source25.record04.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes25 link25 RawClass9.CatalogCodes.checked25
    4 2 Normalizers.Source25.normalizer04 (maps 4) pick04 rows04

def pick05 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes25 5 2 (fun x => (maps 4).get i (Normalizers.Source25.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 4).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes25 5 2 (fun x => (maps 4).get i (Normalizers.Source25.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source25.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link25 (templates 4).family hole 5 2
    Normalizers.Source25.normalizer05 Normalizers.Source25.record05.hole_fixed Normalizers.Source25.record05.center_image Normalizers.Source25.record05.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes25 link25 RawClass9.CatalogCodes.checked25
    5 2 Normalizers.Source25.normalizer05 (maps 4) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source25.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source25Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source25.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source25Center07Q8.complete e he hc hs

def pick08 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes25 8 2 (fun x => (maps 4).get i (Normalizers.Source25.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 4).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes25 8 2 (fun x => (maps 4).get i (Normalizers.Source25.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source25.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link25 (templates 4).family hole 8 2
    Normalizers.Source25.normalizer08 Normalizers.Source25.record08.hole_fixed Normalizers.Source25.record08.center_image Normalizers.Source25.record08.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes25 link25 RawClass9.CatalogCodes.checked25
    8 2 Normalizers.Source25.normalizer08 (maps 4) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source25.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source25Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source25.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source25Center10Q8.complete e he hc hs

def pick11 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩]
def rowCheck11 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick11 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes25 11 2 (fun x => (maps 4).get i (Normalizers.Source25.normalizer11 x))).toFinset)

theorem chunk11_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck11) = true := by decide +kernel
theorem all11 : ((List.finRange (maps 4).length).all rowCheck11) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk11_0
theorem rows11 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick11 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes25 11 2 (fun x => (maps 4).get i (Normalizers.Source25.normalizer11 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all11) i (by simp))

theorem complete11 : SourceComplete domains Normalizers.Source25.record11 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link25 (templates 4).family hole 11 2
    Normalizers.Source25.normalizer11 Normalizers.Source25.record11.hole_fixed Normalizers.Source25.record11.center_image Normalizers.Source25.record11.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes25 link25 RawClass9.CatalogCodes.checked25
    11 2 Normalizers.Source25.normalizer11 (maps 4) pick11 rows11

theorem entries_complete : ∀ r ∈ Normalizers.Source25.entries, SourceComplete domains r := by
  simp only [Normalizers.Source25.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source25
