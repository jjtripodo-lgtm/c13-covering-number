import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source12Center02Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![10,11,8,9,0,1,2,3,6,7,4,5,12]
  invFun := ![4,5,6,7,10,11,8,9,2,3,0,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (2 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link12 2) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes12 2 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes12 2 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link12 2 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes12
    link12 CatalogCodes.checked12 2 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (2 : Point) = hole)
    (hs : transport e (link link12 2) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link12 2 8 e) :=
  source_center_represented raw8 link12 link09 hole 2 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source12Center02Q8
namespace C13.Enumeration.RawClass9.Source12Center03Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![10,11,9,8,0,1,3,2,6,7,5,4,12]
  invFun := ![4,5,7,6,11,10,8,9,3,2,0,1,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (3 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link12 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes12 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes12 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link12 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes12
    link12 CatalogCodes.checked12 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link12 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link12 3 8 e) :=
  source_center_represented raw8 link12 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source12Center03Q8
namespace C13.Enumeration.RawClass9.Source12Center06Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,3,4,5,10,11,8,9,0,1,6,7,12]
  invFun := ![8,9,0,1,2,3,10,11,6,7,4,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (6 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link12 6) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes12 6 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes12 6 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link12 6 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes12
    link12 CatalogCodes.checked12 6 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (6 : Point) = hole)
    (hs : transport e (link link12 6) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link12 6 8 e) :=
  source_center_represented raw8 link12 link09 hole 6 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source12Center06Q8
namespace C13.Enumeration.RawClass9.Source12Center07Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,3,5,4,10,11,9,8,0,1,7,6,12]
  invFun := ![8,9,0,1,3,2,11,10,7,6,4,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (7 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link12 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes12 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes12 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link12 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes12
    link12 CatalogCodes.checked12 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link12 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link12 7 8 e) :=
  source_center_represented raw8 link12 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source12Center07Q8
namespace C13.Enumeration.RawClass9.Source12Center10Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,1,2,3,6,7,4,5,10,11,8,9,12]
  invFun := ![0,1,2,3,6,7,4,5,10,11,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (10 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link12 10) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes12 10 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes12 10 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link12 10 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes12
    link12 CatalogCodes.checked12 10 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (10 : Point) = hole)
    (hs : transport e (link link12 10) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link12 10 8 e) :=
  source_center_represented raw8 link12 link09 hole 10 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source12Center10Q8
namespace C13.Enumeration.RawClass9.Source12Center11Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,1,3,2,6,7,5,4,10,11,9,8,12]
  invFun := ![0,1,3,2,7,6,4,5,11,10,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (11 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link12 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes12 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes12 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link12 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes12
    link12 CatalogCodes.checked12 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link12 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link12 11 8 e) :=
  source_center_represented raw8 link12 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source12Center11Q8
