import C13Enumeration.Canonical.Normalizers.Source18
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source18
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 23).length → (table 23).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 23).length) : Bool :=
  decide (((domains 23).pencil ((table 23).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes18 0 0 (fun x => (maps 23).get i (Normalizers.Source18.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 23).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 23).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 23).length = (((List.finRange (maps 23).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 23).length,
    ((domains 23).pencil ((table 23).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes18 0 0 (fun x => (maps 23).get i (Normalizers.Source18.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source18.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 23) link18 (templates 23).family hole 0 0
    Normalizers.Source18.normalizer00 Normalizers.Source18.record00.hole_fixed Normalizers.Source18.record00.center_image Normalizers.Source18.record00.star_image
    (maps 23) (maps_complete 23) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 23) (table 23)
    RawClass9.CatalogCodes.codes18 link18 RawClass9.CatalogCodes.checked18
    0 0 Normalizers.Source18.normalizer00 (maps 23) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source18.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source18Center01Q8.complete e he hc hs

def pick02 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes18 2 2 (fun x => (maps 12).get i (Normalizers.Source18.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 12).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes18 2 2 (fun x => (maps 12).get i (Normalizers.Source18.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source18.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link18 (templates 12).family hole 2 2
    Normalizers.Source18.normalizer02 Normalizers.Source18.record02.hole_fixed Normalizers.Source18.record02.center_image Normalizers.Source18.record02.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes18 link18 RawClass9.CatalogCodes.checked18
    2 2 Normalizers.Source18.normalizer02 (maps 12) pick02 rows02

theorem complete03 : SourceComplete domains Normalizers.Source18.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source18Center03Q8.complete e he hc hs

def pick04 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes18 4 2 (fun x => (maps 12).get i (Normalizers.Source18.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 12).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes18 4 2 (fun x => (maps 12).get i (Normalizers.Source18.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source18.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link18 (templates 12).family hole 4 2
    Normalizers.Source18.normalizer04 Normalizers.Source18.record04.hole_fixed Normalizers.Source18.record04.center_image Normalizers.Source18.record04.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes18 link18 RawClass9.CatalogCodes.checked18
    4 2 Normalizers.Source18.normalizer04 (maps 12) pick04 rows04

def pick05 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes18 5 2 (fun x => (maps 12).get i (Normalizers.Source18.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 12).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes18 5 2 (fun x => (maps 12).get i (Normalizers.Source18.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source18.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link18 (templates 12).family hole 5 2
    Normalizers.Source18.normalizer05 Normalizers.Source18.record05.hole_fixed Normalizers.Source18.record05.center_image Normalizers.Source18.record05.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes18 link18 RawClass9.CatalogCodes.checked18
    5 2 Normalizers.Source18.normalizer05 (maps 12) pick05 rows05

def pick06 : Fin (maps 8).length → (table 8).Index := ![⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩]
def rowCheck06 (i : Fin (maps 8).length) : Bool :=
  decide (((domains 8).pencil ((table 8).row (pick06 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes18 6 6 (fun x => (maps 8).get i (Normalizers.Source18.normalizer06 x))).toFinset)

theorem chunk06_0 : ((((List.finRange (maps 8).length).drop 0).take 16).all rowCheck06) = true := by decide +kernel
theorem all06 : ((List.finRange (maps 8).length).all rowCheck06) = true := by
  have hsplit : List.finRange (maps 8).length = (((List.finRange (maps 8).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk06_0
theorem rows06 : ∀ i : Fin (maps 8).length,
    ((domains 8).pencil ((table 8).row (pick06 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes18 6 6 (fun x => (maps 8).get i (Normalizers.Source18.normalizer06 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all06) i (by simp))

theorem complete06 : SourceComplete domains Normalizers.Source18.record06 := by
  intro _ e he hc hs
  apply source_center_represented (domains 8) link18 (templates 8).family hole 6 6
    Normalizers.Source18.normalizer06 Normalizers.Source18.record06.hole_fixed Normalizers.Source18.record06.center_image Normalizers.Source18.record06.star_image
    (maps 8) (maps_complete 8) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 8) (table 8)
    RawClass9.CatalogCodes.codes18 link18 RawClass9.CatalogCodes.checked18
    6 6 Normalizers.Source18.normalizer06 (maps 8) pick06 rows06

theorem complete07 : SourceComplete domains Normalizers.Source18.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source18Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source18.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source18Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source18.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source18Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source18.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source18Center10Q6.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source18.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source18Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source18.entries, SourceComplete domains r := by
  simp only [Normalizers.Source18.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source18
