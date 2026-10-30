import C13Enumeration.Canonical.Normalizers.Source36
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source36
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes36 0 2 (fun x => (maps 19).get i (Normalizers.Source36.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 19).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes36 0 2 (fun x => (maps 19).get i (Normalizers.Source36.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source36.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link36 (templates 19).family hole 0 2
    Normalizers.Source36.normalizer00 Normalizers.Source36.record00.hole_fixed Normalizers.Source36.record00.center_image Normalizers.Source36.record00.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes36 link36 RawClass9.CatalogCodes.checked36
    0 2 Normalizers.Source36.normalizer00 (maps 19) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source36.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source36Center01Q8.complete e he hc hs

theorem complete02 : SourceComplete domains Normalizers.Source36.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source36Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source36.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source36Center03Q8.complete e he hc hs

def pick04 : Fin (maps 38).length → (table 38).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 38).length) : Bool :=
  decide (((domains 38).pencil ((table 38).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes36 4 4 (fun x => (maps 38).get i (Normalizers.Source36.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 38).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 38).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 38).length = (((List.finRange (maps 38).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 38).length,
    ((domains 38).pencil ((table 38).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes36 4 4 (fun x => (maps 38).get i (Normalizers.Source36.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source36.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 38) link36 (templates 38).family hole 4 4
    Normalizers.Source36.normalizer04 Normalizers.Source36.record04.hole_fixed Normalizers.Source36.record04.center_image Normalizers.Source36.record04.star_image
    (maps 38) (maps_complete 38) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 38) (table 38)
    RawClass9.CatalogCodes.codes36 link36 RawClass9.CatalogCodes.checked36
    4 4 Normalizers.Source36.normalizer04 (maps 38) pick04 rows04

def pick05 : Fin (maps 39).length → (table 39).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 39).length) : Bool :=
  decide (((domains 39).pencil ((table 39).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes36 5 5 (fun x => (maps 39).get i (Normalizers.Source36.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 39).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 39).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 39).length = (((List.finRange (maps 39).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 39).length,
    ((domains 39).pencil ((table 39).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes36 5 5 (fun x => (maps 39).get i (Normalizers.Source36.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source36.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 39) link36 (templates 39).family hole 5 5
    Normalizers.Source36.normalizer05 Normalizers.Source36.record05.hole_fixed Normalizers.Source36.record05.center_image Normalizers.Source36.record05.star_image
    (maps 39) (maps_complete 39) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 39) (table 39)
    RawClass9.CatalogCodes.codes36 link36 RawClass9.CatalogCodes.checked36
    5 5 Normalizers.Source36.normalizer05 (maps 39) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source36.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source36Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source36.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source36Center07Q8.complete e he hc hs

def pick08 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes36 8 2 (fun x => (maps 19).get i (Normalizers.Source36.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 19).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes36 8 2 (fun x => (maps 19).get i (Normalizers.Source36.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source36.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link36 (templates 19).family hole 8 2
    Normalizers.Source36.normalizer08 Normalizers.Source36.record08.hole_fixed Normalizers.Source36.record08.center_image Normalizers.Source36.record08.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes36 link36 RawClass9.CatalogCodes.checked36
    8 2 Normalizers.Source36.normalizer08 (maps 19) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source36.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source36Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source36.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source36Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source36.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source36Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source36.entries, SourceComplete domains r := by
  simp only [Normalizers.Source36.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source36
