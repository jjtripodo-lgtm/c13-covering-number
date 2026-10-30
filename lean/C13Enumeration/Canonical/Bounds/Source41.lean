import C13Enumeration.Canonical.Normalizers.Source41
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source41
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 44).length → (table 44).Index := ![⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 44).length) : Bool :=
  decide (((domains 44).pencil ((table 44).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes41 0 0 (fun x => (maps 44).get i (Normalizers.Source41.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 44).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 44).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 44).length = (((List.finRange (maps 44).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 44).length,
    ((domains 44).pencil ((table 44).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes41 0 0 (fun x => (maps 44).get i (Normalizers.Source41.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source41.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 44) link41 (templates 44).family hole 0 0
    Normalizers.Source41.normalizer00 Normalizers.Source41.record00.hole_fixed Normalizers.Source41.record00.center_image Normalizers.Source41.record00.star_image
    (maps 44) (maps_complete 44) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 44) (table 44)
    RawClass9.CatalogCodes.codes41 link41 RawClass9.CatalogCodes.checked41
    0 0 Normalizers.Source41.normalizer00 (maps 44) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source41.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source41Center01Q8.complete e he hc hs

theorem complete02 : SourceComplete domains Normalizers.Source41.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source41Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source41.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source41Center03Q8.complete e he hc hs

def pick04 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes41 4 4 (fun x => (maps 17).get i (Normalizers.Source41.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 17).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes41 4 4 (fun x => (maps 17).get i (Normalizers.Source41.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source41.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link41 (templates 17).family hole 4 4
    Normalizers.Source41.normalizer04 Normalizers.Source41.record04.hole_fixed Normalizers.Source41.record04.center_image Normalizers.Source41.record04.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes41 link41 RawClass9.CatalogCodes.checked41
    4 4 Normalizers.Source41.normalizer04 (maps 17) pick04 rows04

def pick05 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes41 5 4 (fun x => (maps 17).get i (Normalizers.Source41.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 17).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes41 5 4 (fun x => (maps 17).get i (Normalizers.Source41.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source41.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link41 (templates 17).family hole 5 4
    Normalizers.Source41.normalizer05 Normalizers.Source41.record05.hole_fixed Normalizers.Source41.record05.center_image Normalizers.Source41.record05.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes41 link41 RawClass9.CatalogCodes.checked41
    5 4 Normalizers.Source41.normalizer05 (maps 17) pick05 rows05

def pick06 : Fin (maps 28).length → (table 28).Index := ![⟨⟨0,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨40,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨40,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩]
def rowCheck06 (i : Fin (maps 28).length) : Bool :=
  decide (((domains 28).pencil ((table 28).row (pick06 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes41 6 8 (fun x => (maps 28).get i (Normalizers.Source41.normalizer06 x))).toFinset)

theorem chunk06_0 : ((((List.finRange (maps 28).length).drop 0).take 16).all rowCheck06) = true := by decide +kernel
theorem all06 : ((List.finRange (maps 28).length).all rowCheck06) = true := by
  have hsplit : List.finRange (maps 28).length = (((List.finRange (maps 28).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk06_0
theorem rows06 : ∀ i : Fin (maps 28).length,
    ((domains 28).pencil ((table 28).row (pick06 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes41 6 8 (fun x => (maps 28).get i (Normalizers.Source41.normalizer06 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all06) i (by simp))

theorem complete06 : SourceComplete domains Normalizers.Source41.record06 := by
  intro _ e he hc hs
  apply source_center_represented (domains 28) link41 (templates 28).family hole 6 8
    Normalizers.Source41.normalizer06 Normalizers.Source41.record06.hole_fixed Normalizers.Source41.record06.center_image Normalizers.Source41.record06.star_image
    (maps 28) (maps_complete 28) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 28) (table 28)
    RawClass9.CatalogCodes.codes41 link41 RawClass9.CatalogCodes.checked41
    6 8 Normalizers.Source41.normalizer06 (maps 28) pick06 rows06

theorem complete07 : SourceComplete domains Normalizers.Source41.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source41Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source41.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source41Center08Q8.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source41.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source41Center09Q8.complete e he hc hs

def pick10 : Fin (maps 28).length → (table 28).Index := ![⟨⟨0,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩]
def rowCheck10 (i : Fin (maps 28).length) : Bool :=
  decide (((domains 28).pencil ((table 28).row (pick10 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes41 10 8 (fun x => (maps 28).get i (Normalizers.Source41.normalizer10 x))).toFinset)

theorem chunk10_0 : ((((List.finRange (maps 28).length).drop 0).take 16).all rowCheck10) = true := by decide +kernel
theorem all10 : ((List.finRange (maps 28).length).all rowCheck10) = true := by
  have hsplit : List.finRange (maps 28).length = (((List.finRange (maps 28).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk10_0
theorem rows10 : ∀ i : Fin (maps 28).length,
    ((domains 28).pencil ((table 28).row (pick10 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes41 10 8 (fun x => (maps 28).get i (Normalizers.Source41.normalizer10 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all10) i (by simp))

theorem complete10 : SourceComplete domains Normalizers.Source41.record10 := by
  intro _ e he hc hs
  apply source_center_represented (domains 28) link41 (templates 28).family hole 10 8
    Normalizers.Source41.normalizer10 Normalizers.Source41.record10.hole_fixed Normalizers.Source41.record10.center_image Normalizers.Source41.record10.star_image
    (maps 28) (maps_complete 28) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 28) (table 28)
    RawClass9.CatalogCodes.codes41 link41 RawClass9.CatalogCodes.checked41
    10 8 Normalizers.Source41.normalizer10 (maps 28) pick10 rows10

theorem complete11 : SourceComplete domains Normalizers.Source41.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source41Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source41.entries, SourceComplete domains r := by
  simp only [Normalizers.Source41.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source41
