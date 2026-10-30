import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table6

namespace C13.Enumeration.RawClass9.Source68Center10Q6
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![3,4,1,2,0,10,5,8,7,11,6,9,12]
  invFun := ![4,2,3,0,1,6,10,8,7,11,5,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (10 : Point) = 6 := by decide +kernel
theorem star_image : transport normalizer (link figure6 10) = link link09 6 := by decide +kernel

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
    (codedEmit CatalogCodes.codes68 10 6
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
      (codedEmit CatalogCodes.codes68 10 6
        (fun x => Template6.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw6 figure6 10 6 normalizer Template6.maps :=
  mapsRepresented_of_code_checks raw6 table6 CatalogCodes.codes68
    figure6 CatalogCodes.checked68 10 6 normalizer Template6.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 6) (hc : e (10 : Point) = hole)
    (hs : transport e (link figure6 10) = link link09 6) :
    ∃ p ∈ raw6.supported.domain.2, RepresentsPencil p (emitPencil figure6 10 6 e) :=
  source_center_represented raw6 figure6 link09 hole 10 6 normalizer
    hole_fixed center_image star_image Template6.maps Template6.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source68Center10Q6
namespace C13.Enumeration.RawClass9.Source68Center11Q6
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![3,1,4,2,0,10,5,7,8,11,9,6,12]
  invFun := ![4,1,3,0,2,6,11,7,8,10,5,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (11 : Point) = 6 := by decide +kernel
theorem star_image : transport normalizer (link figure6 11) = link link09 6 := by decide +kernel

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
    (codedEmit CatalogCodes.codes68 11 6
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
      (codedEmit CatalogCodes.codes68 11 6
        (fun x => Template6.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw6 figure6 11 6 normalizer Template6.maps :=
  mapsRepresented_of_code_checks raw6 table6 CatalogCodes.codes68
    figure6 CatalogCodes.checked68 11 6 normalizer Template6.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 6) (hc : e (11 : Point) = hole)
    (hs : transport e (link figure6 11) = link link09 6) :
    ∃ p ∈ raw6.supported.domain.2, RepresentsPencil p (emitPencil figure6 11 6 e) :=
  source_center_represented raw6 figure6 link09 hole 11 6 normalizer
    hole_fixed center_image star_image Template6.maps Template6.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source68Center11Q6
