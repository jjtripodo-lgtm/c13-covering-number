import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source67Center02Q8
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
theorem star_image : transport normalizer (link link67 2) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨12,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨86,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨66,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨66,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨86,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes67 2 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes67 2 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link67 2 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes67
    link67 CatalogCodes.checked67 2 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (2 : Point) = hole)
    (hs : transport e (link link67 2) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link67 2 8 e) :=
  source_center_represented raw8 link67 link09 hole 2 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source67Center02Q8
namespace C13.Enumeration.RawClass9.Source67Center05Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,0,3,5,10,8,11,9,4,6,1,7,12]
  invFun := ![1,10,0,2,8,3,9,11,5,7,4,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (5 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link67 5) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨12,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨86,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨66,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨66,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨86,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes67 5 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes67 5 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link67 5 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes67
    link67 CatalogCodes.checked67 5 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (5 : Point) = hole)
    (hs : transport e (link link67 5) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link67 5 8 e) :=
  source_center_represented raw8 link67 link09 hole 5 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source67Center05Q8
namespace C13.Enumeration.RawClass9.Source67Center11Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,5,3,0,4,7,1,6,10,9,11,8,12]
  invFun := ![3,6,0,2,4,1,7,5,11,9,8,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (11 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link67 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨12,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨86,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨66,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨66,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨86,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes67 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes67 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link67 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes67
    link67 CatalogCodes.checked67 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link67 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link67 11 8 e) :=
  source_center_represented raw8 link67 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source67Center11Q8
