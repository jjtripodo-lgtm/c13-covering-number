import C13Enumeration.Canonical.Normalizers.Source17
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source17
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 22).length → (table 22).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 22).length) : Bool :=
  decide (((domains 22).pencil ((table 22).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes17 0 0 (fun x => (maps 22).get i (Normalizers.Source17.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 22).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 22).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 22).length = (((List.finRange (maps 22).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 22).length,
    ((domains 22).pencil ((table 22).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes17 0 0 (fun x => (maps 22).get i (Normalizers.Source17.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source17.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 22) link17 (templates 22).family hole 0 0
    Normalizers.Source17.normalizer00 Normalizers.Source17.record00.hole_fixed Normalizers.Source17.record00.center_image Normalizers.Source17.record00.star_image
    (maps 22) (maps_complete 22) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 22) (table 22)
    RawClass9.CatalogCodes.codes17 link17 RawClass9.CatalogCodes.checked17
    0 0 Normalizers.Source17.normalizer00 (maps 22) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source17.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source17Center01Q8.complete e he hc hs

def pick02 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes17 2 2 (fun x => (maps 12).get i (Normalizers.Source17.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 12).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes17 2 2 (fun x => (maps 12).get i (Normalizers.Source17.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source17.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link17 (templates 12).family hole 2 2
    Normalizers.Source17.normalizer02 Normalizers.Source17.record02.hole_fixed Normalizers.Source17.record02.center_image Normalizers.Source17.record02.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes17 link17 RawClass9.CatalogCodes.checked17
    2 2 Normalizers.Source17.normalizer02 (maps 12) pick02 rows02

theorem complete03 : SourceComplete domains Normalizers.Source17.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source17Center03Q8.complete e he hc hs

def pick04 : Fin (maps 22).length → (table 22).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 22).length) : Bool :=
  decide (((domains 22).pencil ((table 22).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes17 4 0 (fun x => (maps 22).get i (Normalizers.Source17.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 22).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 22).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 22).length = (((List.finRange (maps 22).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 22).length,
    ((domains 22).pencil ((table 22).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes17 4 0 (fun x => (maps 22).get i (Normalizers.Source17.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source17.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 22) link17 (templates 22).family hole 4 0
    Normalizers.Source17.normalizer04 Normalizers.Source17.record04.hole_fixed Normalizers.Source17.record04.center_image Normalizers.Source17.record04.star_image
    (maps 22) (maps_complete 22) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 22) (table 22)
    RawClass9.CatalogCodes.codes17 link17 RawClass9.CatalogCodes.checked17
    4 0 Normalizers.Source17.normalizer04 (maps 22) pick04 rows04

def pick05 : Fin (maps 12).length → (table 12).Index := ![⟨⟨0,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 12).length) : Bool :=
  decide (((domains 12).pencil ((table 12).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes17 5 2 (fun x => (maps 12).get i (Normalizers.Source17.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 12).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 12).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 12).length = (((List.finRange (maps 12).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 12).length,
    ((domains 12).pencil ((table 12).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes17 5 2 (fun x => (maps 12).get i (Normalizers.Source17.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source17.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 12) link17 (templates 12).family hole 5 2
    Normalizers.Source17.normalizer05 Normalizers.Source17.record05.hole_fixed Normalizers.Source17.record05.center_image Normalizers.Source17.record05.star_image
    (maps 12) (maps_complete 12) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 12) (table 12)
    RawClass9.CatalogCodes.codes17 link17 RawClass9.CatalogCodes.checked17
    5 2 Normalizers.Source17.normalizer05 (maps 12) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source17.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source17Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source17.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source17Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source17.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source17Center08Q6.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source17.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source17Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source17.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source17Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source17.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source17Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source17.entries, SourceComplete domains r := by
  simp only [Normalizers.Source17.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source17
