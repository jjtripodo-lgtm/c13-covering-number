import C13Enumeration.Canonical.Normalizers.Source13
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source13
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 9).length → (table 9).Index := ![⟨⟨0,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 9).length) : Bool :=
  decide (((domains 9).pencil ((table 9).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes13 0 2 (fun x => (maps 9).get i (Normalizers.Source13.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 9).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 9).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 9).length = (((List.finRange (maps 9).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 9).length,
    ((domains 9).pencil ((table 9).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes13 0 2 (fun x => (maps 9).get i (Normalizers.Source13.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source13.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 9) link13 (templates 9).family hole 0 2
    Normalizers.Source13.normalizer00 Normalizers.Source13.record00.hole_fixed Normalizers.Source13.record00.center_image Normalizers.Source13.record00.star_image
    (maps 9) (maps_complete 9) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 9) (table 9)
    RawClass9.CatalogCodes.codes13 link13 RawClass9.CatalogCodes.checked13
    0 2 Normalizers.Source13.normalizer00 (maps 9) pick00 rows00

def pick01 : Fin (maps 9).length → (table 9).Index := ![⟨⟨0,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 9).length) : Bool :=
  decide (((domains 9).pencil ((table 9).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes13 1 2 (fun x => (maps 9).get i (Normalizers.Source13.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 9).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 9).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 9).length = (((List.finRange (maps 9).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 9).length,
    ((domains 9).pencil ((table 9).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes13 1 2 (fun x => (maps 9).get i (Normalizers.Source13.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source13.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 9) link13 (templates 9).family hole 1 2
    Normalizers.Source13.normalizer01 Normalizers.Source13.record01.hole_fixed Normalizers.Source13.record01.center_image Normalizers.Source13.record01.star_image
    (maps 9) (maps_complete 9) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 9) (table 9)
    RawClass9.CatalogCodes.codes13 link13 RawClass9.CatalogCodes.checked13
    1 2 Normalizers.Source13.normalizer01 (maps 9) pick01 rows01

theorem complete02 : SourceComplete domains Normalizers.Source13.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source13Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source13.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source13Center03Q8.complete e he hc hs

def pick04 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes13 4 2 (fun x => (maps 4).get i (Normalizers.Source13.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 4).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes13 4 2 (fun x => (maps 4).get i (Normalizers.Source13.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source13.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link13 (templates 4).family hole 4 2
    Normalizers.Source13.normalizer04 Normalizers.Source13.record04.hole_fixed Normalizers.Source13.record04.center_image Normalizers.Source13.record04.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes13 link13 RawClass9.CatalogCodes.checked13
    4 2 Normalizers.Source13.normalizer04 (maps 4) pick04 rows04

def pick05 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes13 5 2 (fun x => (maps 4).get i (Normalizers.Source13.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 4).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes13 5 2 (fun x => (maps 4).get i (Normalizers.Source13.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source13.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link13 (templates 4).family hole 5 2
    Normalizers.Source13.normalizer05 Normalizers.Source13.record05.hole_fixed Normalizers.Source13.record05.center_image Normalizers.Source13.record05.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes13 link13 RawClass9.CatalogCodes.checked13
    5 2 Normalizers.Source13.normalizer05 (maps 4) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source13.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source13Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source13.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source13Center07Q8.complete e he hc hs

def pick08 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes13 8 2 (fun x => (maps 4).get i (Normalizers.Source13.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 4).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes13 8 2 (fun x => (maps 4).get i (Normalizers.Source13.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source13.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link13 (templates 4).family hole 8 2
    Normalizers.Source13.normalizer08 Normalizers.Source13.record08.hole_fixed Normalizers.Source13.record08.center_image Normalizers.Source13.record08.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes13 link13 RawClass9.CatalogCodes.checked13
    8 2 Normalizers.Source13.normalizer08 (maps 4) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source13.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source13Center09Q8.complete e he hc hs

def pick10 : Fin (maps 4).length → (table 4).Index := ![⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩]
def rowCheck10 (i : Fin (maps 4).length) : Bool :=
  decide (((domains 4).pencil ((table 4).row (pick10 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes13 10 2 (fun x => (maps 4).get i (Normalizers.Source13.normalizer10 x))).toFinset)

theorem chunk10_0 : ((((List.finRange (maps 4).length).drop 0).take 16).all rowCheck10) = true := by decide +kernel
theorem all10 : ((List.finRange (maps 4).length).all rowCheck10) = true := by
  have hsplit : List.finRange (maps 4).length = (((List.finRange (maps 4).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk10_0
theorem rows10 : ∀ i : Fin (maps 4).length,
    ((domains 4).pencil ((table 4).row (pick10 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes13 10 2 (fun x => (maps 4).get i (Normalizers.Source13.normalizer10 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all10) i (by simp))

theorem complete10 : SourceComplete domains Normalizers.Source13.record10 := by
  intro _ e he hc hs
  apply source_center_represented (domains 4) link13 (templates 4).family hole 10 2
    Normalizers.Source13.normalizer10 Normalizers.Source13.record10.hole_fixed Normalizers.Source13.record10.center_image Normalizers.Source13.record10.star_image
    (maps 4) (maps_complete 4) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 4) (table 4)
    RawClass9.CatalogCodes.codes13 link13 RawClass9.CatalogCodes.checked13
    10 2 Normalizers.Source13.normalizer10 (maps 4) pick10 rows10

theorem complete11 : SourceComplete domains Normalizers.Source13.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source13Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source13.entries, SourceComplete domains r := by
  simp only [Normalizers.Source13.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source13
