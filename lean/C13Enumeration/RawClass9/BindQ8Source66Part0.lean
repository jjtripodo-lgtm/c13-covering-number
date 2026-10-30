import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source66Center03Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![9,10,11,8,0,3,2,5,1,6,7,4,12]
  invFun := ![4,8,6,5,11,7,9,10,3,0,1,2,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (3 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link66 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨64,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨64,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes66 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes66 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link66 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes66
    link66 CatalogCodes.checked66 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link66 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link66 3 8 e) :=
  source_center_represented raw8 link66 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source66Center03Q8
namespace C13.Enumeration.RawClass9.Source66Center06Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![5,0,3,2,10,11,8,9,7,6,1,4,12]
  invFun := ![1,10,3,2,11,0,9,8,6,7,4,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (6 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link66 6) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨64,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨64,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes66 6 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes66 6 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link66 6 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes66
    link66 CatalogCodes.checked66 6 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (6 : Point) = hole)
    (hs : transport e (link link66 6) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link66 6 8 e) :=
  source_center_represented raw8 link66 link09 hole 6 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source66Center06Q8
namespace C13.Enumeration.RawClass9.Source66Center09Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![5,3,0,2,7,1,6,4,10,8,11,9,12]
  invFun := ![2,5,3,1,7,0,6,4,9,11,8,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (9 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link66 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨64,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨64,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes66 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes66 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link66 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes66
    link66 CatalogCodes.checked66 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link66 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link66 9 8 e) :=
  source_center_represented raw8 link66 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source66Center09Q8
