import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source64Center02Q8
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
theorem star_image : transport normalizer (link link64 2) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨12,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨44,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨88,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨124,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨55,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes64 2 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes64 2 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link64 2 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes64
    link64 CatalogCodes.checked64 2 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (2 : Point) = hole)
    (hs : transport e (link link64 2) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link64 2 8 e) :=
  source_center_represented raw8 link64 link09 hole 2 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source64Center02Q8
namespace C13.Enumeration.RawClass9.Source64Center03Q8
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
theorem star_image : transport normalizer (link link64 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨109,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨109,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨66,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨27,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes64 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes64 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link64 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes64
    link64 CatalogCodes.checked64 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link64 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link64 3 8 e) :=
  source_center_represented raw8 link64 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source64Center03Q8
namespace C13.Enumeration.RawClass9.Source64Center07Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![3,0,2,5,10,9,11,8,1,6,4,7,12]
  invFun := ![1,8,2,0,10,3,9,11,7,5,4,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (7 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link64 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨9,by decide +kernel⟩,⟨100,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨78,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨73,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨73,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨78,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨100,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes64 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes64 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link64 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes64
    link64 CatalogCodes.checked64 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link64 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link64 7 8 e) :=
  source_center_represented raw8 link64 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source64Center07Q8
namespace C13.Enumeration.RawClass9.Source64Center09Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,0,3,5,4,6,1,7,10,8,11,9,12]
  invFun := ![1,6,0,2,4,3,5,7,9,11,8,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (9 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link64 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨9,by decide +kernel⟩,⟨124,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨88,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨55,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨44,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes64 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes64 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link64 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes64
    link64 CatalogCodes.checked64 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link64 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link64 9 8 e) :=
  source_center_represented raw8 link64 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source64Center09Q8
namespace C13.Enumeration.RawClass9.Source64Center10Q8
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
theorem star_image : transport normalizer (link link64 10) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨10,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨66,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨27,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨109,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨109,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes64 10 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes64 10 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link64 10 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes64
    link64 CatalogCodes.checked64 10 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (10 : Point) = hole)
    (hs : transport e (link link64 10) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link64 10 8 e) :=
  source_center_represented raw8 link64 link09 hole 10 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source64Center10Q8
