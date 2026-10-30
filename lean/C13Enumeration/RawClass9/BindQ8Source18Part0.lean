import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source18Center01Q8
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
theorem star_image : transport normalizer (link link18 1) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨5,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨74,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨73,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes18 1 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes18 1 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link18 1 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes18
    link18 CatalogCodes.checked18 1 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (1 : Point) = hole)
    (hs : transport e (link link18 1) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link18 1 8 e) :=
  source_center_represented raw8 link18 link09 hole 1 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source18Center01Q8
namespace C13.Enumeration.RawClass9.Source18Center03Q8
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
theorem star_image : transport normalizer (link link18 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨5,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨92,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨57,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨73,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes18 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes18 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link18 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes18
    link18 CatalogCodes.checked18 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link18 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link18 3 8 e) :=
  source_center_represented raw8 link18 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source18Center03Q8
namespace C13.Enumeration.RawClass9.Source18Center07Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,3,1,2,10,9,11,8,6,5,7,4,12]
  invFun := ![0,2,3,1,11,9,8,10,7,5,4,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (7 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link18 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨0,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨100,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨80,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨96,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨74,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes18 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes18 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link18 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes18
    link18 CatalogCodes.checked18 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link18 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link18 7 8 e) :=
  source_center_represented raw8 link18 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source18Center07Q8
namespace C13.Enumeration.RawClass9.Source18Center08Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,2,5,3,4,6,1,7,8,10,9,11,12]
  invFun := ![0,6,1,3,4,2,5,7,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (8 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link18 8) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨9,by decide +kernel⟩,⟨104,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨111,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨110,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨81,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨43,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨85,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes18 8 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes18 8 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link18 8 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes18
    link18 CatalogCodes.checked18 8 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (8 : Point) = hole)
    (hs : transport e (link link18 8) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link18 8 8 e) :=
  source_center_represented raw8 link18 link09 hole 8 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source18Center08Q8
namespace C13.Enumeration.RawClass9.Source18Center09Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,2,3,5,6,4,1,7,10,8,9,11,12]
  invFun := ![0,6,1,2,5,3,4,7,9,10,8,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (9 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link18 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨9,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨112,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨80,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨55,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨92,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes18 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes18 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link18 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes18
    link18 CatalogCodes.checked18 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link18 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link18 9 8 e) :=
  source_center_represented raw8 link18 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source18Center09Q8
namespace C13.Enumeration.RawClass9.Source18Center11Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,5,3,2,6,7,1,4,10,11,9,8,12]
  invFun := ![0,6,3,2,7,1,4,5,11,10,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (11 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link18 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨10,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨88,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨86,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨91,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨113,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨92,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨63,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨66,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes18 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes18 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link18 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes18
    link18 CatalogCodes.checked18 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link18 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link18 11 8 e) :=
  source_center_represented raw8 link18 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source18Center11Q8
