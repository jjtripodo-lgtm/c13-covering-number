import C13Enumeration.Canonical.Normalizers.Source24
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source24
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes24 0 2 (fun x => (maps 4).get i (Normalizers.Source24.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 4).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes24 0 2 (fun x => (maps 4).get i (Normalizers.Source24.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source24.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link24 (templates 4).family hole 0 2
    Normalizers.Source24.normalizer00 Normalizers.Source24.record00.hole_fixed Normalizers.Source24.record00.center_image Normalizers.Source24.record00.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes24 link24 RawClass9.CatalogCodes.checked24
    0 2 Normalizers.Source24.normalizer00 (maps 4) pick00 rows00

def pick01 : Fin (maps 18).length → (table 18).Index := ![⟨⟨0,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 18).length) : Bool :=
  decide (((domains 18).pencil ((table 18).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes24 1 2 (fun x => (maps 18).get i (Normalizers.Source24.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 18).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 18).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 18).length = (((List.finRange (maps 18).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 18).length,
    ((domains 18).pencil ((table 18).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes24 1 2 (fun x => (maps 18).get i (Normalizers.Source24.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source24.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 18) link24 (templates 18).family hole 1 2
    Normalizers.Source24.normalizer01 Normalizers.Source24.record01.hole_fixed Normalizers.Source24.record01.center_image Normalizers.Source24.record01.star_image
    (maps 18) (maps_complete 18) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 18) (table 18)
    RawClass9.CatalogCodes.codes24 link24 RawClass9.CatalogCodes.checked24
    1 2 Normalizers.Source24.normalizer01 (maps 18) pick01 rows01

def pick02 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes24 2 2 (fun x => (maps 4).get i (Normalizers.Source24.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 4).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes24 2 2 (fun x => (maps 4).get i (Normalizers.Source24.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source24.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link24 (templates 4).family hole 2 2
    Normalizers.Source24.normalizer02 Normalizers.Source24.record02.hole_fixed Normalizers.Source24.record02.center_image Normalizers.Source24.record02.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes24 link24 RawClass9.CatalogCodes.checked24
    2 2 Normalizers.Source24.normalizer02 (maps 4) pick02 rows02

theorem complete03 : SourceComplete domains Normalizers.Source24.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source24Center03Q8.complete e he hc hs

def pick04 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes24 4 4 (fun x => (maps 17).get i (Normalizers.Source24.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 17).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes24 4 4 (fun x => (maps 17).get i (Normalizers.Source24.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source24.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link24 (templates 17).family hole 4 4
    Normalizers.Source24.normalizer04 Normalizers.Source24.record04.hole_fixed Normalizers.Source24.record04.center_image Normalizers.Source24.record04.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes24 link24 RawClass9.CatalogCodes.checked24
    4 4 Normalizers.Source24.normalizer04 (maps 17) pick04 rows04

def pick05 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes24 5 4 (fun x => (maps 17).get i (Normalizers.Source24.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 17).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes24 5 4 (fun x => (maps 17).get i (Normalizers.Source24.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source24.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link24 (templates 17).family hole 5 4
    Normalizers.Source24.normalizer05 Normalizers.Source24.record05.hole_fixed Normalizers.Source24.record05.center_image Normalizers.Source24.record05.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes24 link24 RawClass9.CatalogCodes.checked24
    5 4 Normalizers.Source24.normalizer05 (maps 17) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source24.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source24Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source24.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source24Center07Q6.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source24.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source24Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source24.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source24Center09Q8.complete e he hc hs

def pick10 : Fin (maps 10).length → (table 10).Index := ![⟨⟨0,by decide +kernel⟩,⟨40,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩]
def rowCheck10 (i : Fin (maps 10).length) : Bool :=
  decide (((domains 10).pencil ((table 10).row (pick10 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes24 10 2 (fun x => (maps 10).get i (Normalizers.Source24.normalizer10 x))).toFinset)

theorem chunk10_0 : ((((List.finRange (maps 10).length).drop 0).take 16).all rowCheck10) = true := by decide +kernel
theorem all10 : ((List.finRange (maps 10).length).all rowCheck10) = true := by
  have hsplit : List.finRange (maps 10).length = (((List.finRange (maps 10).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk10_0
theorem rows10 : ∀ i : Fin (maps 10).length,
    ((domains 10).pencil ((table 10).row (pick10 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes24 10 2 (fun x => (maps 10).get i (Normalizers.Source24.normalizer10 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all10) i (by simp))

theorem complete10 : SourceComplete domains Normalizers.Source24.record10 := by
  intro _ e he hc hs
  apply source_center_represented (domains 10) link24 (templates 10).family hole 10 2
    Normalizers.Source24.normalizer10 Normalizers.Source24.record10.hole_fixed Normalizers.Source24.record10.center_image Normalizers.Source24.record10.star_image
    (maps 10) (maps_complete 10) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 10) (table 10)
    RawClass9.CatalogCodes.codes24 link24 RawClass9.CatalogCodes.checked24
    10 2 Normalizers.Source24.normalizer10 (maps 10) pick10 rows10

theorem complete11 : SourceComplete domains Normalizers.Source24.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source24Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source24.entries, SourceComplete domains r := by
  simp only [Normalizers.Source24.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source24
