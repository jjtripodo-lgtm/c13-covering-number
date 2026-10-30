import C13Enumeration.Canonical.Normalizers.Source52
import C13Enumeration.Canonical.Domains
import C13Enumeration.Canonical.Maps
namespace C13.Enumeration.Canonical.Bounds.Source52
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def pick00 : Fin (maps 51).length → (table 51).Index := ![⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩]
def rowCheck00 (i : Fin (maps 51).length) : Bool :=
  decide (((domains 51).pencil ((table 51).row (pick00 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes52 0 0 (fun x => (maps 51).get i (Normalizers.Source52.normalizer00 x))).toFinset)

theorem chunk00_0 : ((((List.finRange (maps 51).length).drop 0).take 16).all rowCheck00) = true := by decide +kernel
theorem chunk00_1 : ((((List.finRange (maps 51).length).drop 16).take 16).all rowCheck00) = true := by decide +kernel
theorem all00 : ((List.finRange (maps 51).length).all rowCheck00) = true := by
  have hsplit : List.finRange (maps 51).length = (((List.finRange (maps 51).length).drop 0).take 16) ++ (((List.finRange (maps 51).length).drop 16).take 16) := by decide +kernel
  rw [hsplit]
  simp only [List.all_append,Bool.and_eq_true,and_assoc]
  exact ⟨chunk00_0,chunk00_1⟩
theorem rows00 : ∀ i : Fin (maps 51).length,
    ((domains 51).pencil ((table 51).row (pick00 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes52 0 0 (fun x => (maps 51).get i (Normalizers.Source52.normalizer00 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all00) i (by simp))

theorem complete00 : SourceComplete domains Normalizers.Source52.record00 := by
  intro _ e he hc hs
  apply source_center_represented (domains 51) link52 (templates 51).family hole 0 0
    Normalizers.Source52.normalizer00 Normalizers.Source52.record00.hole_fixed Normalizers.Source52.record00.center_image Normalizers.Source52.record00.star_image
    (maps 51) (maps_complete 51) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 51) (table 51)
    RawClass9.CatalogCodes.codes52 link52 RawClass9.CatalogCodes.checked52
    0 0 Normalizers.Source52.normalizer00 (maps 51) pick00 rows00

theorem complete01 : SourceComplete domains Normalizers.Source52.record01 := by
  intro _ e he hc hs
  exact RawClass9.Source52Center01Q8.complete e he hc hs

theorem complete02 : SourceComplete domains Normalizers.Source52.record02 := by
  intro _ e he hc hs
  exact RawClass9.Source52Center02Q8.complete e he hc hs

theorem complete03 : SourceComplete domains Normalizers.Source52.record03 := by
  intro _ e he hc hs
  exact RawClass9.Source52Center03Q8.complete e he hc hs

def pick04 : Fin (maps 51).length → (table 51).Index := ![⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩]
def rowCheck04 (i : Fin (maps 51).length) : Bool :=
  decide (((domains 51).pencil ((table 51).row (pick04 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes52 4 0 (fun x => (maps 51).get i (Normalizers.Source52.normalizer04 x))).toFinset)

theorem chunk04_0 : ((((List.finRange (maps 51).length).drop 0).take 16).all rowCheck04) = true := by decide +kernel
theorem chunk04_1 : ((((List.finRange (maps 51).length).drop 16).take 16).all rowCheck04) = true := by decide +kernel
theorem all04 : ((List.finRange (maps 51).length).all rowCheck04) = true := by
  have hsplit : List.finRange (maps 51).length = (((List.finRange (maps 51).length).drop 0).take 16) ++ (((List.finRange (maps 51).length).drop 16).take 16) := by decide +kernel
  rw [hsplit]
  simp only [List.all_append,Bool.and_eq_true,and_assoc]
  exact ⟨chunk04_0,chunk04_1⟩
theorem rows04 : ∀ i : Fin (maps 51).length,
    ((domains 51).pencil ((table 51).row (pick04 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes52 4 0 (fun x => (maps 51).get i (Normalizers.Source52.normalizer04 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all04) i (by simp))

theorem complete04 : SourceComplete domains Normalizers.Source52.record04 := by
  intro _ e he hc hs
  apply source_center_represented (domains 51) link52 (templates 51).family hole 4 0
    Normalizers.Source52.normalizer04 Normalizers.Source52.record04.hole_fixed Normalizers.Source52.record04.center_image Normalizers.Source52.record04.star_image
    (maps 51) (maps_complete 51) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 51) (table 51)
    RawClass9.CatalogCodes.codes52 link52 RawClass9.CatalogCodes.checked52
    4 0 Normalizers.Source52.normalizer04 (maps 51) pick04 rows04

theorem complete05 : SourceComplete domains Normalizers.Source52.record05 := by
  intro _ e he hc hs
  exact RawClass9.Source52Center05Q8.complete e he hc hs

theorem complete06 : SourceComplete domains Normalizers.Source52.record06 := by
  intro _ e he hc hs
  exact RawClass9.Source52Center06Q8.complete e he hc hs

theorem complete07 : SourceComplete domains Normalizers.Source52.record07 := by
  intro _ e he hc hs
  exact RawClass9.Source52Center07Q8.complete e he hc hs

def pick08 : Fin (maps 51).length → (table 51).Index := ![⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,⟨⟨0,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩]
def rowCheck08 (i : Fin (maps 51).length) : Bool :=
  decide (((domains 51).pencil ((table 51).row (pick08 i))).toFinset =
    (codedEmit RawClass9.CatalogCodes.codes52 8 0 (fun x => (maps 51).get i (Normalizers.Source52.normalizer08 x))).toFinset)

theorem chunk08_0 : ((((List.finRange (maps 51).length).drop 0).take 16).all rowCheck08) = true := by decide +kernel
theorem chunk08_1 : ((((List.finRange (maps 51).length).drop 16).take 16).all rowCheck08) = true := by decide +kernel
theorem all08 : ((List.finRange (maps 51).length).all rowCheck08) = true := by
  have hsplit : List.finRange (maps 51).length = (((List.finRange (maps 51).length).drop 0).take 16) ++ (((List.finRange (maps 51).length).drop 16).take 16) := by decide +kernel
  rw [hsplit]
  simp only [List.all_append,Bool.and_eq_true,and_assoc]
  exact ⟨chunk08_0,chunk08_1⟩
theorem rows08 : ∀ i : Fin (maps 51).length,
    ((domains 51).pencil ((table 51).row (pick08 i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes52 8 0 (fun x => (maps 51).get i (Normalizers.Source52.normalizer08 x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp all08) i (by simp))

theorem complete08 : SourceComplete domains Normalizers.Source52.record08 := by
  intro _ e he hc hs
  apply source_center_represented (domains 51) link52 (templates 51).family hole 8 0
    Normalizers.Source52.normalizer08 Normalizers.Source52.record08.hole_fixed Normalizers.Source52.record08.center_image Normalizers.Source52.record08.star_image
    (maps 51) (maps_complete 51) ?_ e he hc hs
  exact mapsRepresented_of_code_checks (domains 51) (table 51)
    RawClass9.CatalogCodes.codes52 link52 RawClass9.CatalogCodes.checked52
    8 0 Normalizers.Source52.normalizer08 (maps 51) pick08 rows08

theorem complete09 : SourceComplete domains Normalizers.Source52.record09 := by
  intro _ e he hc hs
  exact RawClass9.Source52Center09Q8.complete e he hc hs

theorem complete10 : SourceComplete domains Normalizers.Source52.record10 := by
  intro _ e he hc hs
  exact RawClass9.Source52Center10Q8.complete e he hc hs

theorem complete11 : SourceComplete domains Normalizers.Source52.record11 := by
  intro _ e he hc hs
  exact RawClass9.Source52Center11Q8.complete e he hc hs

theorem entries_complete : ∀ r ∈ Normalizers.Source52.entries, SourceComplete domains r := by
  simp only [Normalizers.Source52.entries,List.forall_mem_cons]
  exact ⟨complete00,complete01,complete02,complete03,complete04,complete05,complete06,complete07,complete08,complete09,complete10,complete11,(by intro r hr; simp at hr)⟩
end C13.Enumeration.Canonical.Bounds.Source52
