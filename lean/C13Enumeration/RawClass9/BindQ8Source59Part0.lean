import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source59Center02Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![9,10,8,11,0,3,5,2,1,6,4,7,12]
  invFun := ![4,8,7,5,10,6,9,11,2,0,1,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (2 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link59 2) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨12,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨76,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨57,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨90,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨82,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨63,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨98,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes59 2 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes59 2 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link59 2 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes59
    link59 CatalogCodes.checked59 2 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (2 : Point) = hole)
    (hs : transport e (link link59 2) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link59 2 8 e) :=
  source_center_represented raw8 link59 link09 hole 2 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source59Center02Q8
namespace C13.Enumeration.RawClass9.Source59Center03Q8
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
theorem star_image : transport normalizer (link link59 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨63,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨101,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨60,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨112,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨78,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨101,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes59 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes59 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link59 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes59
    link59 CatalogCodes.checked59 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link59 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link59 3 8 e) :=
  source_center_represented raw8 link59 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source59Center03Q8
namespace C13.Enumeration.RawClass9.Source59Center07Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,3,5,2,10,9,11,8,6,1,7,4,12]
  invFun := ![0,9,3,1,11,2,8,10,7,5,4,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (7 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link59 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨57,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨98,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨63,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨78,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨37,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨83,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes59 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes59 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link59 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes59
    link59 CatalogCodes.checked59 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link59 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link59 7 8 e) :=
  source_center_represented raw8 link59 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source59Center07Q8
namespace C13.Enumeration.RawClass9.Source59Center10Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![5,0,3,2,7,6,1,4,10,11,8,9,12]
  invFun := ![1,6,3,2,7,0,5,4,10,11,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (10 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link59 10) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨12,by decide +kernel⟩,⟨55,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨91,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨83,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨78,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨59,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨60,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨105,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨61,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨113,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes59 10 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes59 10 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link59 10 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes59
    link59 CatalogCodes.checked59 10 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (10 : Point) = hole)
    (hs : transport e (link link59 10) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link59 10 8 e) :=
  source_center_represented raw8 link59 link09 hole 10 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source59Center10Q8
