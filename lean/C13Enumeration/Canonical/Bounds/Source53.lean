import C13Enumeration.Canonical.Normalizers.Source53
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source53
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 52).length → (table 52).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 52).length) : Bool :=
  decide (((domains 52).pencil ((table 52).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes53 0 0 (fun x => (maps 52).get i (Normalizers.Source53.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 52).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 52).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 52).length = (((List.finRange (maps 52).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk00_0
theorem rows00 : ∀ i : Fin (maps 52).length,
    ((domains 52).pencil ((table 52).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes53 0 0 (fun x => (maps 52).get i (Normalizers.Source53.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source53.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 52) link53 (templates 52).family hole 0 0
    Normalizers.Source53.normalizer00 Normalizers.Source53.record00.hole_fixed Normalizers.Source53.record00.center_image Normalizers.Source53.record00.star_image
    (maps 52) (maps_complete 52) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 52) (table 52)
    RawClass9.CatalogCodes.codes53 link53 RawClass9.CatalogCodes.checked53
    0 0 Normalizers.Source53.normalizer00 (maps 52) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source53.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source53Center01Q8.complete e he hc hs

theorem complete02 : SourceComplete domains Normalizers.Source53.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source53Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source53.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source53Center03Q8.complete e he hc hs

def pick04 : Fin (maps 28).length → (table 28).Index := ![⟨⟨0,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨12,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨12,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 28).length) : Bool :=
  decide (((domains 28).pencil ((table 28).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes53 4 8 (fun x => (maps 28).get i (Normalizers.Source53.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 28).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 28).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 28).length = (((List.finRange (maps 28).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 28).length,
    ((domains 28).pencil ((table 28).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes53 4 8 (fun x => (maps 28).get i (Normalizers.Source53.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source53.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 28) link53 (templates 28).family hole 4 8
    Normalizers.Source53.normalizer04 Normalizers.Source53.record04.hole_fixed Normalizers.Source53.record04.center_image Normalizers.Source53.record04.star_image
    (maps 28) (maps_complete 28) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 28) (table 28)
    RawClass9.CatalogCodes.codes53 link53 RawClass9.CatalogCodes.checked53
    4 8 Normalizers.Source53.normalizer04 (maps 28) pick04 rows04

def pick05 : Fin (maps 19).length → (table 19).Index := ![⟨⟨0,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩]
def rowCheck05 (i : Fin (maps 19).length) : Bool :=
  decide (((domains 19).pencil ((table 19).row (pick05 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes53 5 2 (fun x => (maps 19).get i (Normalizers.Source53.normalizer05 x))).toFinset)

theorem chunk05_0 : ((((List.finRange (maps 19).length).drop 0).take 16).all rowCheck05) = true := by decide +kernel
theorem all05 : ((List.finRange (maps 19).length).all rowCheck05) = true := by
  have hsplit : List.finRange (maps 19).length = (((List.finRange (maps 19).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk05_0
theorem rows05 : ∀ i : Fin (maps 19).length,
    ((domains 19).pencil ((table 19).row (pick05 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes53 5 2 (fun x => (maps 19).get i (Normalizers.Source53.normalizer05 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all05) i (by simp))

theorem complete05 : SourceComplete domains Normalizers.Source53.record05 := by
  intro _ e he hc hs
  apply source_center_represented (domains 19) link53 (templates 19).family hole 5 2
    Normalizers.Source53.normalizer05 Normalizers.Source53.record05.hole_fixed Normalizers.Source53.record05.center_image Normalizers.Source53.record05.star_image
    (maps 19) (maps_complete 19) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 19) (table 19)
    RawClass9.CatalogCodes.codes53 link53 RawClass9.CatalogCodes.checked53
    5 2 Normalizers.Source53.normalizer05 (maps 19) pick05 rows05

theorem complete06 : SourceComplete domains Normalizers.Source53.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source53Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source53.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source53Center07Q8.complete e he hc hs

def pick08 : Fin (maps 26).length → (table 26).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 26).length) : Bool :=
  decide (((domains 26).pencil ((table 26).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes53 8 0 (fun x => (maps 26).get i (Normalizers.Source53.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 26).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 26).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 26).length = (((List.finRange (maps 26).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 26).length,
    ((domains 26).pencil ((table 26).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes53 8 0 (fun x => (maps 26).get i (Normalizers.Source53.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source53.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 26) link53 (templates 26).family hole 8 0
    Normalizers.Source53.normalizer08 Normalizers.Source53.record08.hole_fixed Normalizers.Source53.record08.center_image Normalizers.Source53.record08.star_image
    (maps 26) (maps_complete 26) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 26) (table 26)
    RawClass9.CatalogCodes.codes53 link53 RawClass9.CatalogCodes.checked53
    8 0 Normalizers.Source53.normalizer08 (maps 26) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source53.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source53Center09Q6.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source53.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source53Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source53.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source53Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source53.entries, SourceComplete domains r := by
  simp only [Normalizers.Source53.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source53
