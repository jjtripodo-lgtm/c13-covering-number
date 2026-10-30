import C13Enumeration.Canonical.Normalizers.Source15
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source15
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 20).length → (table 20).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 20).length) : Bool :=
  decide (((domains 20).pencil ((table 20).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes15 0 0 (fun x => (maps 20).get i (Normalizers.Source15.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 20).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 20).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 20).length = (((List.finRange (maps 20).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 20).length,
    ((domains 20).pencil ((table 20).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes15 0 0 (fun x => (maps 20).get i (Normalizers.Source15.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source15.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 20) link15 (templates 20).family hole 0 0
    Normalizers.Source15.normalizer00 Normalizers.Source15.record00.hole_fixed Normalizers.Source15.record00.center_image Normalizers.Source15.record00.star_image
    (maps 20) (maps_complete 20) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 20) (table 20)
    RawClass9.CatalogCodes.codes15 link15 RawClass9.CatalogCodes.checked15
    0 0 Normalizers.Source15.normalizer00 (maps 20) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source15.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source15Center01Q8.complete e he hc hs

def pick02 : Fin (maps 20).length → (table 20).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 20).length) : Bool :=
  decide (((domains 20).pencil ((table 20).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes15 2 0 (fun x => (maps 20).get i (Normalizers.Source15.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 20).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 20).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 20).length = (((List.finRange (maps 20).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 20).length,
    ((domains 20).pencil ((table 20).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes15 2 0 (fun x => (maps 20).get i (Normalizers.Source15.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source15.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 20) link15 (templates 20).family hole 2 0
    Normalizers.Source15.normalizer02 Normalizers.Source15.record02.hole_fixed Normalizers.Source15.record02.center_image Normalizers.Source15.record02.star_image
    (maps 20) (maps_complete 20) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 20) (table 20)
    RawClass9.CatalogCodes.codes15 link15 RawClass9.CatalogCodes.checked15
    2 0 Normalizers.Source15.normalizer02 (maps 20) pick02 rows02

theorem complete03 : SourceComplete domains Normalizers.Source15.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source15Center03Q8.complete e he hc hs

def pick04 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes15 4 2 (fun x => (maps 12).get i (Normalizers.Source15.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 12).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes15 4 2 (fun x => (maps 12).get i (Normalizers.Source15.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source15.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link15 (templates 12).family hole 4 2
    Normalizers.Source15.normalizer04 Normalizers.Source15.record04.hole_fixed Normalizers.Source15.record04.center_image Normalizers.Source15.record04.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes15 link15 RawClass9.CatalogCodes.checked15
    4 2 Normalizers.Source15.normalizer04 (maps 12) pick04 rows04

def pick05 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes15 5 2 (fun x => (maps 12).get i (Normalizers.Source15.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 12).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes15 5 2 (fun x => (maps 12).get i (Normalizers.Source15.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source15.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link15 (templates 12).family hole 5 2
    Normalizers.Source15.normalizer05 Normalizers.Source15.record05.hole_fixed Normalizers.Source15.record05.center_image Normalizers.Source15.record05.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes15 link15 RawClass9.CatalogCodes.checked15
    5 2 Normalizers.Source15.normalizer05 (maps 12) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source15.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source15Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source15.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source15Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source15.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source15Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source15.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source15Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source15.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source15Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source15.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source15Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source15.entries, SourceComplete domains r := by
  simp only [Normalizers.Source15.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source15
