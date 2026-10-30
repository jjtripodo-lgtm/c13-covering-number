import C13Enumeration.Canonical.Normalizers.Source63
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source63
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem complete00 : SourceComplete domains Normalizers.Source63.record00 := by
  intro _ e he hc hs
  exact RawClass9.Source63Center00Q6.complete e he hc hs

def pick01 : Fin (maps 58).length → (table 58).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck01 (i : Fin (maps 58).length) : Bool :=
  decide (((domains 58).pencil ((table 58).row (pick01 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes63 1 1 (fun x => (maps 58).get i (Normalizers.Source63.normalizer01 x))).toFinset)

theorem chunk01_0 : ((((List.finRange (maps 58).length).drop 0).take 16).all rowCheck01) = true := by decide +kernel
theorem all01 : ((List.finRange (maps 58).length).all rowCheck01) = true := by
  have hsplit : List.finRange (maps 58).length = (((List.finRange (maps 58).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk01_0
theorem rows01 : ∀ i : Fin (maps 58).length,
    ((domains 58).pencil ((table 58).row (pick01 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes63 1 1 (fun x => (maps 58).get i (Normalizers.Source63.normalizer01 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all01) i (by simp))

theorem complete01 : SourceComplete domains Normalizers.Source63.record01 := by
  intro _ e he hc hs
  apply source_center_represented (domains 58) link63 (templates 58).family hole 1 1
    Normalizers.Source63.normalizer01 Normalizers.Source63.record01.hole_fixed Normalizers.Source63.record01.center_image Normalizers.Source63.record01.star_image
    (maps 58) (maps_complete 58) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 58) (table 58)
    RawClass9.CatalogCodes.codes63 link63 RawClass9.CatalogCodes.checked63
    1 1 Normalizers.Source63.normalizer01 (maps 58) pick01 rows01

theorem complete02 : SourceComplete domains Normalizers.Source63.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source63Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source63.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source63Center03Q8.complete e he hc hs

def pick04 : Fin (maps 58).length → (table 58).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 58).length) : Bool :=
  decide (((domains 58).pencil ((table 58).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes63 4 1 (fun x => (maps 58).get i (Normalizers.Source63.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 58).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 58).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 58).length = (((List.finRange (maps 58).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk04_0
theorem rows04 : ∀ i : Fin (maps 58).length,
    ((domains 58).pencil ((table 58).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes63 4 1 (fun x => (maps 58).get i (Normalizers.Source63.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source63.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 58) link63 (templates 58).family hole 4 1
    Normalizers.Source63.normalizer04 Normalizers.Source63.record04.hole_fixed Normalizers.Source63.record04.center_image Normalizers.Source63.record04.star_image
    (maps 58) (maps_complete 58) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 58) (table 58)
    RawClass9.CatalogCodes.codes63 link63 RawClass9.CatalogCodes.checked63
    4 1 Normalizers.Source63.normalizer04 (maps 58) pick04 rows04

theorem complete05 : SourceComplete domains Normalizers.Source63.record05 := by
  intro _ e he hc hs
  exact RawClass9.Source63Center05Q6.complete e he hc hs

theorem complete06 : SourceComplete domains Normalizers.Source63.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source63Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source63.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source63Center07Q8.complete e he hc hs

def pick08 : Fin (maps 58).length → (table 58).Index := ![⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 58).length) : Bool :=
  decide (((domains 58).pencil ((table 58).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes63 8 1 (fun x => (maps 58).get i (Normalizers.Source63.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 58).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 58).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 58).length = (((List.finRange (maps 58).length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk08_0
theorem rows08 : ∀ i : Fin (maps 58).length,
    ((domains 58).pencil ((table 58).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes63 8 1 (fun x => (maps 58).get i (Normalizers.Source63.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source63.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 58) link63 (templates 58).family hole 8 1
    Normalizers.Source63.normalizer08 Normalizers.Source63.record08.hole_fixed Normalizers.Source63.record08.center_image Normalizers.Source63.record08.star_image
    (maps 58) (maps_complete 58) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 58) (table 58)
    RawClass9.CatalogCodes.codes63 link63 RawClass9.CatalogCodes.checked63
    8 1 Normalizers.Source63.normalizer08 (maps 58) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source63.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source63Center09Q6.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source63.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source63Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source63.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source63Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source63.entries, SourceComplete domains r := by
  simp only [Normalizers.Source63.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source63
