import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source25Center01Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![9,8,10,11,0,1,3,2,5,4,6,7,12]
  invFun := ![4,5,7,6,9,8,10,11,1,0,2,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (1 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link25 1) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨20,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨46,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨107,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes25 1 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes25 1 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link25 1 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes25
    link25 CatalogCodes.checked25 1 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (1 : Point) = hole)
    (hs : transport e (link link25 1) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link25 1 8 e) :=
  source_center_represented raw8 link25 link09 hole 1 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source25Center01Q8
namespace C13.Enumeration.RawClass9.Source25Center03Q8
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
theorem star_image : transport normalizer (link link25 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨20,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨46,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨107,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes25 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes25 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link25 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes25
    link25 CatalogCodes.checked25 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link25 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link25 3 8 e) :=
  source_center_represented raw8 link25 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source25Center03Q8
namespace C13.Enumeration.RawClass9.Source25Center06Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,5,4,3,10,9,8,11,0,7,6,1,12]
  invFun := ![8,11,0,3,2,1,10,9,6,5,4,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (6 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link25 6) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨26,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨46,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨107,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes25 6 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes25 6 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link25 6 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes25
    link25 CatalogCodes.checked25 6 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (6 : Point) = hole)
    (hs : transport e (link link25 6) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link25 6 8 e) :=
  source_center_represented raw8 link25 link09 hole 6 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source25Center06Q8
namespace C13.Enumeration.RawClass9.Source25Center07Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![5,2,3,4,9,10,11,8,0,7,6,1,12]
  invFun := ![8,11,1,2,3,0,10,9,7,4,5,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (7 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link25 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨26,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨46,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨107,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes25 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes25 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link25 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes25
    link25 CatalogCodes.checked25 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link25 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link25 7 8 e) :=
  source_center_represented raw8 link25 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source25Center07Q8
namespace C13.Enumeration.RawClass9.Source25Center09Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,2,1,3,6,4,7,5,10,8,11,9,12]
  invFun := ![0,2,1,3,5,7,4,6,9,11,8,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (9 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link25 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨20,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨46,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨107,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes25 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes25 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link25 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes25
    link25 CatalogCodes.checked25 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link25 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link25 9 8 e) :=
  source_center_represented raw8 link25 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source25Center09Q8
namespace C13.Enumeration.RawClass9.Source25Center10Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,3,1,2,5,6,4,7,9,10,8,11,12]
  invFun := ![0,2,3,1,6,4,5,7,10,8,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (10 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link25 10) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨23,by decide +kernel⟩,⟨107,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨46,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes25 10 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes25 10 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link25 10 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes25
    link25 CatalogCodes.checked25 10 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (10 : Point) = hole)
    (hs : transport e (link link25 10) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link25 10 8 e) :=
  source_center_represented raw8 link25 link09 hole 10 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source25Center10Q8
