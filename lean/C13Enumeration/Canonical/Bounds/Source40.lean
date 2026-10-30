import C13Enumeration.Canonical.Normalizers.Source40
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source40
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 42).length → (table 42).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 42).length) : Bool :=
  decide (((domains 42).pencil ((table 42).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes40 0 0 (fun x => (maps 42).get i (Normalizers.Source40.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 42).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 42).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 42).length = (((List.finRange (maps 42).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 42).length,
    ((domains 42).pencil ((table 42).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes40 0 0 (fun x => (maps 42).get i (Normalizers.Source40.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source40.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 42) link40 (templates 42).family hole 0 0
    Normalizers.Source40.normalizer00 Normalizers.Source40.record00.hole_fixed Normalizers.Source40.record00.center_image Normalizers.Source40.record00.star_image
    (maps 42) (maps_complete 42) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 42) (table 42)
    RawClass9.CatalogCodes.codes40 link40 RawClass9.CatalogCodes.checked40
    0 0 Normalizers.Source40.normalizer00 (maps 42) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source40.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source40Center01Q8.complete e he hc hs

theorem complete02 : SourceComplete domains Normalizers.Source40.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source40Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source40.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source40Center03Q8.complete e he hc hs

def pick04 : Fin (maps 43).length → (table 43).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 43).length) : Bool :=
  decide (((domains 43).pencil ((table 43).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes40 4 4 (fun x => (maps 43).get i (Normalizers.Source40.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 43).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 43).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 43).length = (((List.finRange (maps 43).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 43).length,
    ((domains 43).pencil ((table 43).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes40 4 4 (fun x => (maps 43).get i (Normalizers.Source40.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source40.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 43) link40 (templates 43).family hole 4 4
    Normalizers.Source40.normalizer04 Normalizers.Source40.record04.hole_fixed Normalizers.Source40.record04.center_image Normalizers.Source40.record04.star_image
    (maps 43) (maps_complete 43) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 43) (table 43)
    RawClass9.CatalogCodes.codes40 link40 RawClass9.CatalogCodes.checked40
    4 4 Normalizers.Source40.normalizer04 (maps 43) pick04 rows04

def pick05 : Fin (maps 17).length → (table 17).Index := ![⟨⟨0,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 17).length) : Bool :=
  decide (((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes40 5 4 (fun x => (maps 17).get i (Normalizers.Source40.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 17).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 17).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 17).length = (((List.finRange (maps 17).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 17).length,
    ((domains 17).pencil ((table 17).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes40 5 4 (fun x => (maps 17).get i (Normalizers.Source40.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source40.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 17) link40 (templates 17).family hole 5 4
    Normalizers.Source40.normalizer05 Normalizers.Source40.record05.hole_fixed Normalizers.Source40.record05.center_image Normalizers.Source40.record05.star_image
    (maps 17) (maps_complete 17) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 17) (table 17)
    RawClass9.CatalogCodes.codes40 link40 RawClass9.CatalogCodes.checked40
    5 4 Normalizers.Source40.normalizer05 (maps 17) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source40.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source40Center06Q6.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source40.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source40Center07Q8.complete e he hc hs

theorem complete08 : SourceComplete domains Normalizers.Source40.record08 := by
  intro _ e he hc hs
  exact RawClass9.Source40Center08Q6.complete e he hc hs

theorem complete09 : SourceComplete domains Normalizers.Source40.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source40Center09Q8.complete e he hc hs

def pick10 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩]
def rowCheck10 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick10 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes40 10 2 (fun x => (maps 19).get i (Normalizers.Source40.normalizer10 x))).toFinset)

theorem chunk10_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck10) = true := by decide +kernel
theorem all10 : ((List.finRange (maps 19).length).all rowCheck10) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk10_0
theorem rows10 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick10 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes40 10 2 (fun x => (maps 19).get i (Normalizers.Source40.normalizer10 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all10) i (by simp))

theorem complete10 : SourceComplete domains Normalizers.Source40.record10 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link40 (templates 19).family hole 10 2
    Normalizers.Source40.normalizer10 Normalizers.Source40.record10.hole_fixed Normalizers.Source40.record10.center_image Normalizers.Source40.record10.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes40 link40 RawClass9.CatalogCodes.checked40
    10 2 Normalizers.Source40.normalizer10 (maps 19) pick10 rows10

theorem complete11 : SourceComplete domains Normalizers.Source40.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source40Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source40.entries, SourceComplete domains r := by
  simp only [Normalizers.Source40.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source40
