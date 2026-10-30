import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source11Center03Q8
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
theorem star_image : transport normalizer (link link11 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨27,by decide +kernel⟩,⟨59,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨85,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨64,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨45,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨59,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨64,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨85,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨45,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨60,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨81,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨81,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨60,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes11 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes11 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link11 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes11
    link11 CatalogCodes.checked11 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link11 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link11 3 8 e) :=
  source_center_represented raw8 link11 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source11Center03Q8
namespace C13.Enumeration.RawClass9.Source11Center06Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![5,2,0,3,9,10,8,11,4,7,1,6,12]
  invFun := ![2,10,1,3,8,0,11,9,6,4,5,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (6 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link11 6) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨10,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨60,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨60,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨111,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨44,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨99,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨67,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes11 6 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes11 6 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link11 6 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes11
    link11 CatalogCodes.checked11 6 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (6 : Point) = hole)
    (hs : transport e (link link11 6) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link11 6 8 e) :=
  source_center_represented raw8 link11 link09 hole 6 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source11Center06Q8
namespace C13.Enumeration.RawClass9.Source11Center07Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,5,0,3,9,10,11,8,7,4,1,6,12]
  invFun := ![2,10,0,3,9,1,11,8,7,4,5,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (7 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link11 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨10,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨60,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨60,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨111,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨44,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨99,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨67,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes11 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes11 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link11 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes11
    link11 CatalogCodes.checked11 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link11 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link11 7 8 e) :=
  source_center_represented raw8 link11 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source11Center07Q8
namespace C13.Enumeration.RawClass9.Source11Center08Q8
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
theorem star_image : transport normalizer (link link11 8) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨2,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨82,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨74,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨60,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨101,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨59,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨85,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨43,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes11 8 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes11 8 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link11 8 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes11
    link11 CatalogCodes.checked11 8 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (8 : Point) = hole)
    (hs : transport e (link link11 8) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link11 8 8 e) :=
  source_center_represented raw8 link11 link09 hole 8 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source11Center08Q8
namespace C13.Enumeration.RawClass9.Source11Center09Q8
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
theorem star_image : transport normalizer (link link11 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨5,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨59,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨85,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨43,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨82,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨74,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨101,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨60,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes11 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes11 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link11 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes11
    link11 CatalogCodes.checked11 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link11 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link11 9 8 e) :=
  source_center_represented raw8 link11 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source11Center09Q8
namespace C13.Enumeration.RawClass9.Source11Center11Q8
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
theorem star_image : transport normalizer (link link11 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨5,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨77,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨57,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨118,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨77,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨57,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨118,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes11 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes11 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link11 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes11
    link11 CatalogCodes.checked11 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link11 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link11 11 8 e) :=
  source_center_represented raw8 link11 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source11Center11Q8
