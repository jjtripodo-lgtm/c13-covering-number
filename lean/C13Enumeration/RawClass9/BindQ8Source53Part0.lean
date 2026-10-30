import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source53Center01Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![9,8,10,11,0,5,3,2,1,4,6,7,12]
  invFun := ![4,8,7,6,9,5,10,11,1,0,2,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (1 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link53 1) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨12,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨43,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨43,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨81,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨81,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes53 1 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes53 1 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link53 1 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes53
    link53 CatalogCodes.checked53 1 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (1 : Point) = hole)
    (hs : transport e (link link53 1) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link53 1 8 e) :=
  source_center_represented raw8 link53 link09 hole 1 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source53Center01Q8
namespace C13.Enumeration.RawClass9.Source53Center02Q8
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
theorem star_image : transport normalizer (link link53 2) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨109,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨63,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨59,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes53 2 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes53 2 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link53 2 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes53
    link53 CatalogCodes.checked53 2 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (2 : Point) = hole)
    (hs : transport e (link link53 2) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link53 2 8 e) :=
  source_center_represented raw8 link53 link09 hole 2 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source53Center02Q8
namespace C13.Enumeration.RawClass9.Source53Center03Q8
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
theorem star_image : transport normalizer (link link53 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨109,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨63,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨59,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes53 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes53 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link53 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes53
    link53 CatalogCodes.checked53 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link53 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link53 3 8 e) :=
  source_center_represented raw8 link53 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source53Center03Q8
namespace C13.Enumeration.RawClass9.Source53Center06Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,3,5,2,9,10,8,11,1,6,4,7,12]
  invFun := ![0,8,3,1,10,2,9,11,6,4,5,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (6 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link53 6) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨9,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨99,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨77,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨66,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨88,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨127,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨67,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨89,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes53 6 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes53 6 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link53 6 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes53
    link53 CatalogCodes.checked53 6 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (6 : Point) = hole)
    (hs : transport e (link link53 6) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link53 6 8 e) :=
  source_center_represented raw8 link53 link09 hole 6 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source53Center06Q8
namespace C13.Enumeration.RawClass9.Source53Center07Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,3,2,5,9,10,11,8,1,6,7,4,12]
  invFun := ![0,8,2,1,11,3,9,10,7,4,5,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (7 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link53 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨9,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨99,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨77,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨66,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨88,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨127,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨67,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨89,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes53 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes53 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link53 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes53
    link53 CatalogCodes.checked53 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link53 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link53 7 8 e) :=
  source_center_represented raw8 link53 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source53Center07Q8
namespace C13.Enumeration.RawClass9.Source53Center10Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,3,2,5,6,1,4,7,10,9,8,11,12]
  invFun := ![0,5,2,1,6,3,4,7,10,9,8,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (10 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link53 10) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨10,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨46,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨45,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨73,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨109,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨77,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes53 10 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes53 10 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link53 10 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes53
    link53 CatalogCodes.checked53 10 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (10 : Point) = hole)
    (hs : transport e (link link53 10) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link53 10 8 e) :=
  source_center_represented raw8 link53 link09 hole 10 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source53Center10Q8
namespace C13.Enumeration.RawClass9.Source53Center11Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,3,5,2,6,1,7,4,10,9,11,8,12]
  invFun := ![0,5,3,1,7,2,4,6,11,9,8,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (11 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link53 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨10,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨46,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨45,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨73,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨109,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨77,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes53 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes53 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link53 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes53
    link53 CatalogCodes.checked53 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link53 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link53 11 8 e) :=
  source_center_represented raw8 link53 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source53Center11Q8
