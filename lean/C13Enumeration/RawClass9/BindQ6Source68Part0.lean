import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table6

namespace C13.Enumeration.RawClass9.Source68Center00Q6
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![6,2,8,4,0,10,5,1,11,7,3,9,12]
  invFun := ![4,7,1,10,3,6,0,9,2,11,5,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (0 : Point) = 6 := by decide +kernel
theorem star_image : transport normalizer (link figure6 0) = link link09 6 := by decide +kernel

def pick : Fin Template6.maps.length → table6.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template6.maps.length) : Bool :=
  decide ((raw6.pencil (table6.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes68 0 6
      (fun x => Template6.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template6.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk1_checked : ((((List.finRange Template6.maps.length).drop 16).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk2_checked : ((((List.finRange Template6.maps.length).drop 32).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk3_checked : ((((List.finRange Template6.maps.length).drop 48).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk4_checked : ((((List.finRange Template6.maps.length).drop 64).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk5_checked : ((((List.finRange Template6.maps.length).drop 80).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template6.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template6.maps.length = (((List.finRange Template6.maps.length).drop 0).take 16) ++ (((List.finRange Template6.maps.length).drop 16).take 16) ++ (((List.finRange Template6.maps.length).drop 32).take 16) ++ (((List.finRange Template6.maps.length).drop 48).take 16) ++ (((List.finRange Template6.maps.length).drop 64).take 16) ++ (((List.finRange Template6.maps.length).drop 80).take 16) := by decide +kernel
  rw [hsplit]
  simp only [List.all_append,Bool.and_eq_true,and_assoc]
  exact ⟨chunk0_checked,chunk1_checked,chunk2_checked,chunk3_checked,chunk4_checked,chunk5_checked⟩

theorem codes_checked : ∀ i : Fin Template6.maps.length,
    (raw6.pencil (table6.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes68 0 6
        (fun x => Template6.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw6 figure6 0 6 normalizer Template6.maps :=
  mapsRepresented_of_code_checks raw6 table6 CatalogCodes.codes68
    figure6 CatalogCodes.checked68 0 6 normalizer Template6.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 6) (hc : e (0 : Point) = hole)
    (hs : transport e (link figure6 0) = link link09 6) :
    ∃ p ∈ raw6.supported.domain.2, RepresentsPencil p (emitPencil figure6 0 6 e) :=
  source_center_represented raw6 figure6 link09 hole 0 6 normalizer
    hole_fixed center_image star_image Template6.maps Template6.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source68Center00Q6
namespace C13.Enumeration.RawClass9.Source68Center01Q6
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,6,8,4,0,10,1,5,11,3,7,9,12]
  invFun := ![4,6,0,9,3,7,1,10,2,11,5,8,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (1 : Point) = 6 := by decide +kernel
theorem star_image : transport normalizer (link figure6 1) = link link09 6 := by decide +kernel

def pick : Fin Template6.maps.length → table6.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template6.maps.length) : Bool :=
  decide ((raw6.pencil (table6.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes68 1 6
      (fun x => Template6.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template6.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk1_checked : ((((List.finRange Template6.maps.length).drop 16).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk2_checked : ((((List.finRange Template6.maps.length).drop 32).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk3_checked : ((((List.finRange Template6.maps.length).drop 48).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk4_checked : ((((List.finRange Template6.maps.length).drop 64).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk5_checked : ((((List.finRange Template6.maps.length).drop 80).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template6.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template6.maps.length = (((List.finRange Template6.maps.length).drop 0).take 16) ++ (((List.finRange Template6.maps.length).drop 16).take 16) ++ (((List.finRange Template6.maps.length).drop 32).take 16) ++ (((List.finRange Template6.maps.length).drop 48).take 16) ++ (((List.finRange Template6.maps.length).drop 64).take 16) ++ (((List.finRange Template6.maps.length).drop 80).take 16) := by decide +kernel
  rw [hsplit]
  simp only [List.all_append,Bool.and_eq_true,and_assoc]
  exact ⟨chunk0_checked,chunk1_checked,chunk2_checked,chunk3_checked,chunk4_checked,chunk5_checked⟩

theorem codes_checked : ∀ i : Fin Template6.maps.length,
    (raw6.pencil (table6.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes68 1 6
        (fun x => Template6.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw6 figure6 1 6 normalizer Template6.maps :=
  mapsRepresented_of_code_checks raw6 table6 CatalogCodes.codes68
    figure6 CatalogCodes.checked68 1 6 normalizer Template6.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 6) (hc : e (1 : Point) = hole)
    (hs : transport e (link figure6 1) = link link09 6) :
    ∃ p ∈ raw6.supported.domain.2, RepresentsPencil p (emitPencil figure6 1 6 e) :=
  source_center_represented raw6 figure6 link09 hole 1 6 normalizer
    hole_fixed center_image star_image Template6.maps Template6.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source68Center01Q6
namespace C13.Enumeration.RawClass9.Source68Center02Q6
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,8,6,4,0,10,1,11,5,3,9,7,12]
  invFun := ![4,6,0,9,3,8,2,11,1,10,5,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (2 : Point) = 6 := by decide +kernel
theorem star_image : transport normalizer (link figure6 2) = link link09 6 := by decide +kernel

def pick : Fin Template6.maps.length → table6.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template6.maps.length) : Bool :=
  decide ((raw6.pencil (table6.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes68 2 6
      (fun x => Template6.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template6.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk1_checked : ((((List.finRange Template6.maps.length).drop 16).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk2_checked : ((((List.finRange Template6.maps.length).drop 32).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk3_checked : ((((List.finRange Template6.maps.length).drop 48).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk4_checked : ((((List.finRange Template6.maps.length).drop 64).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk5_checked : ((((List.finRange Template6.maps.length).drop 80).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template6.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template6.maps.length = (((List.finRange Template6.maps.length).drop 0).take 16) ++ (((List.finRange Template6.maps.length).drop 16).take 16) ++ (((List.finRange Template6.maps.length).drop 32).take 16) ++ (((List.finRange Template6.maps.length).drop 48).take 16) ++ (((List.finRange Template6.maps.length).drop 64).take 16) ++ (((List.finRange Template6.maps.length).drop 80).take 16) := by decide +kernel
  rw [hsplit]
  simp only [List.all_append,Bool.and_eq_true,and_assoc]
  exact ⟨chunk0_checked,chunk1_checked,chunk2_checked,chunk3_checked,chunk4_checked,chunk5_checked⟩

theorem codes_checked : ∀ i : Fin Template6.maps.length,
    (raw6.pencil (table6.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes68 2 6
        (fun x => Template6.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw6 figure6 2 6 normalizer Template6.maps :=
  mapsRepresented_of_code_checks raw6 table6 CatalogCodes.codes68
    figure6 CatalogCodes.checked68 2 6 normalizer Template6.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 6) (hc : e (2 : Point) = hole)
    (hs : transport e (link figure6 2) = link link09 6) :
    ∃ p ∈ raw6.supported.domain.2, RepresentsPencil p (emitPencil figure6 2 6 e) :=
  source_center_represented raw6 figure6 link09 hole 2 6 normalizer
    hole_fixed center_image star_image Template6.maps Template6.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source68Center02Q6
namespace C13.Enumeration.RawClass9.Source68Center03Q6
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![4,5,7,6,0,10,2,3,1,8,9,11,12]
  invFun := ![4,8,6,7,0,1,3,2,9,10,5,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (3 : Point) = 6 := by decide +kernel
theorem star_image : transport normalizer (link figure6 3) = link link09 6 := by decide +kernel

def pick : Fin Template6.maps.length → table6.Index := ![
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template6.maps.length) : Bool :=
  decide ((raw6.pencil (table6.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes68 3 6
      (fun x => Template6.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template6.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk1_checked : ((((List.finRange Template6.maps.length).drop 16).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk2_checked : ((((List.finRange Template6.maps.length).drop 32).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk3_checked : ((((List.finRange Template6.maps.length).drop 48).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk4_checked : ((((List.finRange Template6.maps.length).drop 64).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk5_checked : ((((List.finRange Template6.maps.length).drop 80).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template6.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template6.maps.length = (((List.finRange Template6.maps.length).drop 0).take 16) ++ (((List.finRange Template6.maps.length).drop 16).take 16) ++ (((List.finRange Template6.maps.length).drop 32).take 16) ++ (((List.finRange Template6.maps.length).drop 48).take 16) ++ (((List.finRange Template6.maps.length).drop 64).take 16) ++ (((List.finRange Template6.maps.length).drop 80).take 16) := by decide +kernel
  rw [hsplit]
  simp only [List.all_append,Bool.and_eq_true,and_assoc]
  exact ⟨chunk0_checked,chunk1_checked,chunk2_checked,chunk3_checked,chunk4_checked,chunk5_checked⟩

theorem codes_checked : ∀ i : Fin Template6.maps.length,
    (raw6.pencil (table6.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes68 3 6
        (fun x => Template6.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw6 figure6 3 6 normalizer Template6.maps :=
  mapsRepresented_of_code_checks raw6 table6 CatalogCodes.codes68
    figure6 CatalogCodes.checked68 3 6 normalizer Template6.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 6) (hc : e (3 : Point) = hole)
    (hs : transport e (link figure6 3) = link link09 6) :
    ∃ p ∈ raw6.supported.domain.2, RepresentsPencil p (emitPencil figure6 3 6 e) :=
  source_center_represented raw6 figure6 link09 hole 3 6 normalizer
    hole_fixed center_image star_image Template6.maps Template6.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source68Center03Q6
