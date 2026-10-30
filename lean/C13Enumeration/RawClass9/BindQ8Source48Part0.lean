import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source48Center01Q8
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
theorem star_image : transport normalizer (link link48 1) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨5,by decide +kernel⟩,⟨44,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨68,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨77,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨100,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨40,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨111,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨79,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨86,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨110,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨57,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨98,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes48 1 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes48 1 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link48 1 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes48
    link48 CatalogCodes.checked48 1 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (1 : Point) = hole)
    (hs : transport e (link link48 1) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link48 1 8 e) :=
  source_center_represented raw8 link48 link09 hole 1 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source48Center01Q8
namespace C13.Enumeration.RawClass9.Source48Center03Q8
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
theorem star_image : transport normalizer (link link48 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨4,by decide +kernel⟩,⟨127,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨69,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨89,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨69,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨84,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨64,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨67,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes48 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes48 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link48 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes48
    link48 CatalogCodes.checked48 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link48 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link48 3 8 e) :=
  source_center_represented raw8 link48 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source48Center03Q8
namespace C13.Enumeration.RawClass9.Source48Center07Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,5,3,2,10,11,9,8,6,7,1,4,12]
  invFun := ![0,10,3,2,11,1,8,9,7,6,4,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (7 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link48 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨82,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨67,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨45,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨104,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨88,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes48 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes48 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link48 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes48
    link48 CatalogCodes.checked48 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link48 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link48 7 8 e) :=
  source_center_represented raw8 link48 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source48Center07Q8
namespace C13.Enumeration.RawClass9.Source48Center09Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![3,2,0,5,6,7,1,4,9,8,10,11,12]
  invFun := ![2,6,1,0,7,3,4,5,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (9 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link48 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨74,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨74,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨100,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨79,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨77,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨105,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨73,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨81,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes48 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes48 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link48 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes48
    link48 CatalogCodes.checked48 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link48 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link48 9 8 e) :=
  source_center_represented raw8 link48 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source48Center09Q8
namespace C13.Enumeration.RawClass9.Source48Center11Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,5,0,3,7,4,1,6,9,10,11,8,12]
  invFun := ![2,6,0,3,5,1,7,4,11,8,9,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (11 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link48 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨27,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨78,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨37,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨89,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨86,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨101,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes48 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes48 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link48 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes48
    link48 CatalogCodes.checked48 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link48 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link48 11 8 e) :=
  source_center_represented raw8 link48 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source48Center11Q8
