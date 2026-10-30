import C13Enumeration.Canonical.Normalizers.Source10
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source10
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 9).length → (table 9).Index := ![⟨⟨0,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 9).length) : Bool :=
  decide (((domains 9).pencil ((table 9).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes10 0 2 (fun x => (maps 9).get i (Normalizers.Source10.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 9).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 9).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 9).length = (((List.finRange (maps 9).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 9).length,
    ((domains 9).pencil ((table 9).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes10 0 2 (fun x => (maps 9).get i (Normalizers.Source10.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source10.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 9) link10 (templates 9).family hole 0 2
    Normalizers.Source10.normalizer00 Normalizers.Source10.record00.hole_fixed Normalizers.Source10.record00.center_image Normalizers.Source10.record00.star_image
    (maps 9) (maps_complete 9) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 9) (table 9)
    RawClass9.CatalogCodes.codes10 link10 RawClass9.CatalogCodes.checked10
    0 2 Normalizers.Source10.normalizer00 (maps 9) pick00 rows00

def pick01 : Fin (maps 9).length → (table 9).Index := ![⟨⟨0,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 9).length) : Bool :=
  decide (((domains 9).pencil ((table 9).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes10 1 2 (fun x => (maps 9).get i (Normalizers.Source10.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 9).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 9).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 9).length = (((List.finRange (maps 9).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 9).length,
    ((domains 9).pencil ((table 9).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes10 1 2 (fun x => (maps 9).get i (Normalizers.Source10.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source10.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 9) link10 (templates 9).family hole 1 2
    Normalizers.Source10.normalizer01 Normalizers.Source10.record01.hole_fixed Normalizers.Source10.record01.center_image Normalizers.Source10.record01.star_image
    (maps 9) (maps_complete 9) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 9) (table 9)
    RawClass9.CatalogCodes.codes10 link10 RawClass9.CatalogCodes.checked10
    1 2 Normalizers.Source10.normalizer01 (maps 9) pick01 rows01

def pick02 : Fin (maps 18).length → (table 18).Index := ![⟨⟨0,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck02 (i : Fin (maps 18).length) : Bool :=
  decide (((domains 18).pencil ((table 18).row (pick02 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes10 2 2 (fun x => (maps 18).get i (Normalizers.Source10.normalizer02 x))).toFinset)

theorem chunk02_0 : ((((List.finRange (maps 18).length).drop 0).take 16).all rowCheck02) = true := by decide +kernel
theorem all02 : ((List.finRange (maps 18).length).all rowCheck02) = true := by
  have hsplit : List.finRange (maps 18).length = (((List.finRange (maps 18).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk02_0
theorem rows02 : ∀ i : Fin (maps 18).length,
    ((domains 18).pencil ((table 18).row (pick02 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes10 2 2 (fun x => (maps 18).get i (Normalizers.Source10.normalizer02 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all02) i (by simp))

theorem complete02 : SourceComplete domains Normalizers.Source10.record02 := by
  intro _ e he hc hs
  apply source_center_represented (domains 18) link10 (templates 18).family hole 2 2
    Normalizers.Source10.normalizer02 Normalizers.Source10.record02.hole_fixed Normalizers.Source10.record02.center_image Normalizers.Source10.record02.star_image
    (maps 18) (maps_complete 18) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 18) (table 18)
    RawClass9.CatalogCodes.codes10 link10 RawClass9.CatalogCodes.checked10
    2 2 Normalizers.Source10.normalizer02 (maps 18) pick02 rows02

theorem complete03 : SourceComplete domains Normalizers.Source10.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source10Center03Q8.complete e he hc hs

def pick04 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes10 4 4 (fun x => (maps 17).get i (Normalizers.Source10.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 17).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes10 4 4 (fun x => (maps 17).get i (Normalizers.Source10.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source10.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link10 (templates 17).family hole 4 4
    Normalizers.Source10.normalizer04 Normalizers.Source10.record04.hole_fixed Normalizers.Source10.record04.center_image Normalizers.Source10.record04.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes10 link10 RawClass9.CatalogCodes.checked10
    4 4 Normalizers.Source10.normalizer04 (maps 17) pick04 rows04

def pick05 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes10 5 4 (fun x => (maps 17).get i (Normalizers.Source10.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 17).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes10 5 4 (fun x => (maps 17).get i (Normalizers.Source10.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source10.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link10 (templates 17).family hole 5 4
    Normalizers.Source10.normalizer05 Normalizers.Source10.record05.hole_fixed Normalizers.Source10.record05.center_image Normalizers.Source10.record05.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes10 link10 RawClass9.CatalogCodes.checked10
    5 4 Normalizers.Source10.normalizer05 (maps 17) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source10.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source10Center06Q6.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source10.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source10Center07Q8.complete e he hc hs

def pick08 : Fin (maps 10).length → (table 10).Index := ![⟨⟨0,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 10).length) : Bool :=
  decide (((domains 10).pencil ((table 10).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes10 8 2 (fun x => (maps 10).get i (Normalizers.Source10.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 10).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 10).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 10).length = (((List.finRange (maps 10).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 10).length,
    ((domains 10).pencil ((table 10).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes10 8 2 (fun x => (maps 10).get i (Normalizers.Source10.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source10.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 10) link10 (templates 10).family hole 8 2
    Normalizers.Source10.normalizer08 Normalizers.Source10.record08.hole_fixed Normalizers.Source10.record08.center_image Normalizers.Source10.record08.star_image
    (maps 10) (maps_complete 10) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 10) (table 10)
    RawClass9.CatalogCodes.codes10 link10 RawClass9.CatalogCodes.checked10
    8 2 Normalizers.Source10.normalizer08 (maps 10) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source10.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source10Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source10.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source10Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source10.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source10Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source10.entries, SourceComplete domains r := by
  simp only [Normalizers.Source10.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source10
