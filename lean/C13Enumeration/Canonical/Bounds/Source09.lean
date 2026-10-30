import C13Enumeration.Canonical.Normalizers.Source09
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source09
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 16).length → (table 16).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 16).length) : Bool :=
  decide (((domains 16).pencil ((table 16).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes09 0 0 (fun x => (maps 16).get i (Normalizers.Source09.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 16).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 16).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 16).length = (((List.finRange (maps 16).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 16).length,
    ((domains 16).pencil ((table 16).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes09 0 0 (fun x => (maps 16).get i (Normalizers.Source09.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source09.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 16) link09 (templates 16).family hole 0 0
    Normalizers.Source09.normalizer00 Normalizers.Source09.record00.hole_fixed Normalizers.Source09.record00.center_image Normalizers.Source09.record00.star_image
    (maps 16) (maps_complete 16) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 16) (table 16)
    RawClass9.CatalogCodes.codes09 link09 RawClass9.CatalogCodes.checked09
    0 0 Normalizers.Source09.normalizer00 (maps 16) pick00 rows00

def pick01 : Fin (maps 9).length → (table 9).Index := ![⟨⟨0,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 9).length) : Bool :=
  decide (((domains 9).pencil ((table 9).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes09 1 2 (fun x => (maps 9).get i (Normalizers.Source09.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 9).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 9).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 9).length = (((List.finRange (maps 9).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 9).length,
    ((domains 9).pencil ((table 9).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes09 1 2 (fun x => (maps 9).get i (Normalizers.Source09.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source09.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 9) link09 (templates 9).family hole 1 2
    Normalizers.Source09.normalizer01 Normalizers.Source09.record01.hole_fixed Normalizers.Source09.record01.center_image Normalizers.Source09.record01.star_image
    (maps 9) (maps_complete 9) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 9) (table 9)
    RawClass9.CatalogCodes.codes09 link09 RawClass9.CatalogCodes.checked09
    1 2 Normalizers.Source09.normalizer01 (maps 9) pick01 rows01

theorem complete02 : SourceComplete domains Normalizers.Source09.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source09Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source09.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source09Center03Q8.complete e he hc hs

def pick04 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes09 4 4 (fun x => (maps 17).get i (Normalizers.Source09.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 17).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes09 4 4 (fun x => (maps 17).get i (Normalizers.Source09.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source09.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link09 (templates 17).family hole 4 4
    Normalizers.Source09.normalizer04 Normalizers.Source09.record04.hole_fixed Normalizers.Source09.record04.center_image Normalizers.Source09.record04.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes09 link09 RawClass9.CatalogCodes.checked09
    4 4 Normalizers.Source09.normalizer04 (maps 17) pick04 rows04

def pick05 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes09 5 4 (fun x => (maps 17).get i (Normalizers.Source09.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 17).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes09 5 4 (fun x => (maps 17).get i (Normalizers.Source09.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source09.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link09 (templates 17).family hole 5 4
    Normalizers.Source09.normalizer05 Normalizers.Source09.record05.hole_fixed Normalizers.Source09.record05.center_image Normalizers.Source09.record05.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes09 link09 RawClass9.CatalogCodes.checked09
    5 4 Normalizers.Source09.normalizer05 (maps 17) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source09.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source09Center06Q6.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source09.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source09Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source09.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source09Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source09.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source09Center09Q8.complete e he hc hs

def pick10 : Fin (maps 8).length → (table 8).Index := ![⟨⟨0,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩]
def rowCheck10 (i : Fin (maps 8).length) : Bool :=
  decide (((domains 8).pencil ((table 8).row (pick10 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes09 10 6 (fun x => (maps 8).get i (Normalizers.Source09.normalizer10 x))).toFinset)

theorem chunk10_0 : ((((List.finRange (maps 8).length).drop 0).take 16).all rowCheck10) = true := by decide +kernel
theorem all10 : ((List.finRange (maps 8).length).all rowCheck10) = true := by
  have hsplit : List.finRange (maps 8).length = (((List.finRange (maps 8).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk10_0
theorem rows10 : ∀ i : Fin (maps 8).length,
    ((domains 8).pencil ((table 8).row (pick10 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes09 10 6 (fun x => (maps 8).get i (Normalizers.Source09.normalizer10 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all10) i (by simp))

theorem complete10 : SourceComplete domains Normalizers.Source09.record10 := by
  intro _ e he hc hs
  apply source_center_represented (domains 8) link09 (templates 8).family hole 10 6
    Normalizers.Source09.normalizer10 Normalizers.Source09.record10.hole_fixed Normalizers.Source09.record10.center_image Normalizers.Source09.record10.star_image
    (maps 8) (maps_complete 8) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 8) (table 8)
    RawClass9.CatalogCodes.codes09 link09 RawClass9.CatalogCodes.checked09
    10 6 Normalizers.Source09.normalizer10 (maps 8) pick10 rows10

theorem complete11 : SourceComplete domains Normalizers.Source09.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source09Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source09.entries, SourceComplete domains r := by
  simp only [Normalizers.Source09.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source09
