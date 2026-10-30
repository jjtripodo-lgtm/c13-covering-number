import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source01Center02Q8
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
theorem star_image : transport normalizer (link link01 2) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨27,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes01 2 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes01 2 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link01 2 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes01
    link01 CatalogCodes.checked01 2 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (2 : Point) = hole)
    (hs : transport e (link link01 2) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link01 2 8 e) :=
  source_center_represented raw8 link01 link09 hole 2 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source01Center02Q8
namespace C13.Enumeration.RawClass9.Source01Center03Q8
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
theorem star_image : transport normalizer (link link01 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨27,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes01 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes01 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link01 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes01
    link01 CatalogCodes.checked01 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link01 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link01 3 8 e) :=
  source_center_represented raw8 link01 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source01Center03Q8
namespace C13.Enumeration.RawClass9.Source01Center06Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,1,2,3,10,11,8,9,6,7,4,5,12]
  invFun := ![0,1,2,3,10,11,8,9,6,7,4,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (6 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link01 6) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨79,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨79,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨79,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨79,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes01 6 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes01 6 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link01 6 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes01
    link01 CatalogCodes.checked01 6 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (6 : Point) = hole)
    (hs : transport e (link link01 6) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link01 6 8 e) :=
  source_center_represented raw8 link01 link09 hole 6 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source01Center06Q8
namespace C13.Enumeration.RawClass9.Source01Center07Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,1,3,2,10,11,9,8,6,7,5,4,12]
  invFun := ![0,1,3,2,11,10,8,9,7,6,4,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (7 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link01 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨79,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨79,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨79,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨79,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes01 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes01 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link01 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes01
    link01 CatalogCodes.checked01 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link01 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link01 7 8 e) :=
  source_center_represented raw8 link01 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source01Center07Q8
namespace C13.Enumeration.RawClass9.Source01Center08Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,1,2,3,4,5,6,7,8,9,10,11,12]
  invFun := ![0,1,2,3,4,5,6,7,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (8 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link01 8) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes01 8 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes01 8 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link01 8 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes01
    link01 CatalogCodes.checked01 8 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (8 : Point) = hole)
    (hs : transport e (link link01 8) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link01 8 8 e) :=
  source_center_represented raw8 link01 link09 hole 8 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source01Center08Q8
namespace C13.Enumeration.RawClass9.Source01Center09Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  invFun := ![0,1,3,2,5,4,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (9 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link01 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes01 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes01 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link01 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes01
    link01 CatalogCodes.checked01 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link01 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link01 9 8 e) :=
  source_center_represented raw8 link01 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source01Center09Q8
namespace C13.Enumeration.RawClass9.Source01Center10Q8
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
theorem star_image : transport normalizer (link link01 10) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨61,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨61,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨61,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨61,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes01 10 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes01 10 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link01 10 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes01
    link01 CatalogCodes.checked01 10 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (10 : Point) = hole)
    (hs : transport e (link link01 10) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link01 10 8 e) :=
  source_center_represented raw8 link01 link09 hole 10 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source01Center10Q8
namespace C13.Enumeration.RawClass9.Source01Center11Q8
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
theorem star_image : transport normalizer (link link01 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨61,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨61,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨61,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨61,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes01 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes01 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link01 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes01
    link01 CatalogCodes.checked01 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link01 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link01 11 8 e) :=
  source_center_represented raw8 link01 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source01Center11Q8
