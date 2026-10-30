import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source65Center03Q8
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
theorem star_image : transport normalizer (link link65 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨12,by decide +kernel⟩,⟨43,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨86,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨74,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨66,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨89,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨49,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨127,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes65 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes65 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link65 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes65
    link65 CatalogCodes.checked65 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link65 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link65 3 8 e) :=
  source_center_represented raw8 link65 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source65Center03Q8
namespace C13.Enumeration.RawClass9.Source65Center06Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![3,0,5,2,10,9,8,11,1,6,7,4,12]
  invFun := ![1,8,3,0,11,2,9,10,6,5,4,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (6 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link65 6) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨12,by decide +kernel⟩,⟨43,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨86,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨74,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨66,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨89,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨49,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨127,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes65 6 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes65 6 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link65 6 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes65
    link65 CatalogCodes.checked65 6 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (6 : Point) = hole)
    (hs : transport e (link link65 6) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link65 6 8 e) :=
  source_center_represented raw8 link65 link09 hole 6 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source65Center06Q8
namespace C13.Enumeration.RawClass9.Source65Center10Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,5,0,3,4,7,6,1,10,9,8,11,12]
  invFun := ![2,7,0,3,4,1,6,5,10,9,8,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (10 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link65 10) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨12,by decide +kernel⟩,⟨27,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨74,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨124,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨49,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨96,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨74,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨124,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨27,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨96,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨49,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes65 10 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes65 10 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link65 10 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes65
    link65 CatalogCodes.checked65 10 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (10 : Point) = hole)
    (hs : transport e (link link65 10) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link65 10 8 e) :=
  source_center_represented raw8 link65 link09 hole 10 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source65Center10Q8
namespace C13.Enumeration.RawClass9.Source65Center11Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![5,2,0,3,7,4,6,1,10,9,11,8,12]
  invFun := ![2,7,1,3,5,0,6,4,11,9,8,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (11 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link65 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨118,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨58,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨99,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨99,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨58,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨118,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes65 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes65 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link65 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes65
    link65 CatalogCodes.checked65 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link65 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link65 11 8 e) :=
  source_center_represented raw8 link65 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source65Center11Q8
