import C13Enumeration.Canonical.Normalizers.Source46
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source46
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 18).length → (table 18).Index := ![⟨⟨0,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 18).length) : Bool :=
  decide (((domains 18).pencil ((table 18).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes46 0 2 (fun x => (maps 18).get i (Normalizers.Source46.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 18).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 18).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 18).length = (((List.finRange (maps 18).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 18).length,
    ((domains 18).pencil ((table 18).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes46 0 2 (fun x => (maps 18).get i (Normalizers.Source46.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source46.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 18) link46 (templates 18).family hole 0 2
    Normalizers.Source46.normalizer00 Normalizers.Source46.record00.hole_fixed Normalizers.Source46.record00.center_image Normalizers.Source46.record00.star_image
    (maps 18) (maps_complete 18) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 18) (table 18)
    RawClass9.CatalogCodes.codes46 link46 RawClass9.CatalogCodes.checked46
    0 2 Normalizers.Source46.normalizer00 (maps 18) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source46.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source46Center01Q8.complete e he hc hs

def pick02 : Fin (maps 8).length → (table 8).Index := ![⟨⟨0,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 8).length) : Bool :=
  decide (((domains 8).pencil ((table 8).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes46 2 6 (fun x => (maps 8).get i (Normalizers.Source46.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 8).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 8).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 8).length = (((List.finRange (maps 8).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 8).length,
    ((domains 8).pencil ((table 8).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes46 2 6 (fun x => (maps 8).get i (Normalizers.Source46.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source46.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 8) link46 (templates 8).family hole 2 6
    Normalizers.Source46.normalizer02 Normalizers.Source46.record02.hole_fixed Normalizers.Source46.record02.center_image Normalizers.Source46.record02.star_image
    (maps 8) (maps_complete 8) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 8) (table 8)
    RawClass9.CatalogCodes.codes46 link46 RawClass9.CatalogCodes.checked46
    2 6 Normalizers.Source46.normalizer02 (maps 8) pick02 rows02

theorem complete03 : SourceComplete domains Normalizers.Source46.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source46Center03Q8.complete e he hc hs

def pick04 : Fin (maps 47).length → (table 47).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 47).length) : Bool :=
  decide (((domains 47).pencil ((table 47).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes46 4 4 (fun x => (maps 47).get i (Normalizers.Source46.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 47).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 47).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 47).length = (((List.finRange (maps 47).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 47).length,
    ((domains 47).pencil ((table 47).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes46 4 4 (fun x => (maps 47).get i (Normalizers.Source46.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source46.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 47) link46 (templates 47).family hole 4 4
    Normalizers.Source46.normalizer04 Normalizers.Source46.record04.hole_fixed Normalizers.Source46.record04.center_image Normalizers.Source46.record04.star_image
    (maps 47) (maps_complete 47) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 47) (table 47)
    RawClass9.CatalogCodes.codes46 link46 RawClass9.CatalogCodes.checked46
    4 4 Normalizers.Source46.normalizer04 (maps 47) pick04 rows04

def pick05 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes46 5 4 (fun x => (maps 17).get i (Normalizers.Source46.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 17).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes46 5 4 (fun x => (maps 17).get i (Normalizers.Source46.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source46.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link46 (templates 17).family hole 5 4
    Normalizers.Source46.normalizer05 Normalizers.Source46.record05.hole_fixed Normalizers.Source46.record05.center_image Normalizers.Source46.record05.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes46 link46 RawClass9.CatalogCodes.checked46
    5 4 Normalizers.Source46.normalizer05 (maps 17) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source46.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source46Center06Q6.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source46.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source46Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source46.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source46Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source46.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source46Center09Q8.complete e he hc hs

def pick10 : Fin (maps 34).length → (table 34).Index := ![⟨⟨0,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩]
def rowCheck10 (i : Fin (maps 34).length) : Bool :=
  decide (((domains 34).pencil ((table 34).row (pick10 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes46 10 8 (fun x => (maps 34).get i (Normalizers.Source46.normalizer10 x))).toFinset)

theorem chunk10_0 : ((((List.finRange (maps 34).length).drop 0).take 16).all rowCheck10) = true := by decide +kernel
theorem all10 : ((List.finRange (maps 34).length).all rowCheck10) = true := by
  have hsplit : List.finRange (maps 34).length = (((List.finRange (maps 34).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk10_0
theorem rows10 : ∀ i : Fin (maps 34).length,
    ((domains 34).pencil ((table 34).row (pick10 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes46 10 8 (fun x => (maps 34).get i (Normalizers.Source46.normalizer10 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all10) i (by simp))

theorem complete10 : SourceComplete domains Normalizers.Source46.record10 := by
  intro _ e he hc hs
  apply source_center_represented (domains 34) link46 (templates 34).family hole 10 8
    Normalizers.Source46.normalizer10 Normalizers.Source46.record10.hole_fixed Normalizers.Source46.record10.center_image Normalizers.Source46.record10.star_image
    (maps 34) (maps_complete 34) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 34) (table 34)
    RawClass9.CatalogCodes.codes46 link46 RawClass9.CatalogCodes.checked46
    10 8 Normalizers.Source46.normalizer10 (maps 34) pick10 rows10

theorem complete11 : SourceComplete domains Normalizers.Source46.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source46Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source46.entries, SourceComplete domains r := by
  simp only [Normalizers.Source46.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source46
