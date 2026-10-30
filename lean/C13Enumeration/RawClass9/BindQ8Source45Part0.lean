import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source45Center02Q8
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
theorem star_image : transport normalizer (link link45 2) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨5,by decide +kernel⟩,⟨78,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨104,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨63,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨86,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨110,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨67,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨91,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes45 2 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes45 2 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link45 2 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes45
    link45 CatalogCodes.checked45 2 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (2 : Point) = hole)
    (hs : transport e (link link45 2) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link45 2 8 e) :=
  source_center_represented raw8 link45 link09 hole 2 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source45Center02Q8
namespace C13.Enumeration.RawClass9.Source45Center03Q8
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
theorem star_image : transport normalizer (link link45 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨2,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨110,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨67,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨91,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨78,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨63,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨104,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨86,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes45 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes45 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link45 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes45
    link45 CatalogCodes.checked45 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link45 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link45 3 8 e) :=
  source_center_represented raw8 link45 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source45Center03Q8
namespace C13.Enumeration.RawClass9.Source45Center08Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,0,3,5,6,4,7,1,8,10,9,11,12]
  invFun := ![1,7,0,2,5,3,4,6,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (8 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link45 8) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨10,by decide +kernel⟩,⟨112,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨69,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨109,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨58,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨27,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨107,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨77,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨57,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes45 8 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes45 8 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link45 8 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes45
    link45 CatalogCodes.checked45 8 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (8 : Point) = hole)
    (hs : transport e (link link45 8) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link45 8 8 e) :=
  source_center_represented raw8 link45 link09 hole 8 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source45Center08Q8
namespace C13.Enumeration.RawClass9.Source45Center09Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,0,5,3,4,6,7,1,10,8,9,11,12]
  invFun := ![1,7,0,3,4,2,5,6,9,10,8,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (9 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link45 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨10,by decide +kernel⟩,⟨112,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨69,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨109,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨58,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨27,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨107,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨77,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨57,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes45 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes45 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link45 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes45
    link45 CatalogCodes.checked45 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link45 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link45 9 8 e) :=
  source_center_represented raw8 link45 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source45Center09Q8
namespace C13.Enumeration.RawClass9.Source45Center11Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![5,0,2,3,7,6,4,1,10,11,9,8,12]
  invFun := ![1,7,2,3,6,0,5,4,11,10,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (11 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link45 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨12,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes45 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes45 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link45 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes45
    link45 CatalogCodes.checked45 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link45 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link45 11 8 e) :=
  source_center_represented raw8 link45 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source45Center11Q8
