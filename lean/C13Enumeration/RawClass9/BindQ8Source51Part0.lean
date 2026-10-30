import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source51Center01Q8
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
theorem star_image : transport normalizer (link link51 1) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨0,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨61,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨57,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨104,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨44,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨81,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes51 1 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes51 1 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link51 1 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes51
    link51 CatalogCodes.checked51 1 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (1 : Point) = hole)
    (hs : transport e (link link51 1) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link51 1 8 e) :=
  source_center_represented raw8 link51 link09 hole 1 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source51Center01Q8
namespace C13.Enumeration.RawClass9.Source51Center02Q8
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
theorem star_image : transport normalizer (link link51 2) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨0,by decide +kernel⟩,⟨46,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨110,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨46,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨49,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨68,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨90,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨92,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes51 2 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes51 2 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link51 2 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes51
    link51 CatalogCodes.checked51 2 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (2 : Point) = hole)
    (hs : transport e (link link51 2) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link51 2 8 e) :=
  source_center_represented raw8 link51 link09 hole 2 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source51Center02Q8
namespace C13.Enumeration.RawClass9.Source51Center03Q8
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
theorem star_image : transport normalizer (link link51 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨0,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨67,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨45,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes51 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes51 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link51 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes51
    link51 CatalogCodes.checked51 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link51 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link51 3 8 e) :=
  source_center_represented raw8 link51 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source51Center03Q8
namespace C13.Enumeration.RawClass9.Source51Center08Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![4,2,3,5,0,6,7,1,8,10,11,9,12]
  invFun := ![4,7,1,2,0,3,5,6,8,11,9,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (8 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link51 8) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨24,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨68,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨90,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨49,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨110,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨46,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨46,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨92,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes51 8 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes51 8 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link51 8 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes51
    link51 CatalogCodes.checked51 8 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (8 : Point) = hole)
    (hs : transport e (link link51 8) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link51 8 8 e) :=
  source_center_represented raw8 link51 link09 hole 8 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source51Center08Q8
namespace C13.Enumeration.RawClass9.Source51Center09Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,4,5,3,0,6,7,1,10,8,9,11,12]
  invFun := ![4,7,0,3,1,2,5,6,9,10,8,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (9 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link51 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨24,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨61,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨44,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨104,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨57,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨81,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes51 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes51 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link51 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes51
    link51 CatalogCodes.checked51 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link51 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link51 9 8 e) :=
  source_center_represented raw8 link51 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source51Center09Q8
namespace C13.Enumeration.RawClass9.Source51Center11Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![5,2,3,4,0,7,6,1,9,10,11,8,12]
  invFun := ![4,7,1,2,3,0,6,5,11,8,9,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (11 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link51 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨24,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨0,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨67,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨45,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes51 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes51 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link51 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes51
    link51 CatalogCodes.checked51 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link51 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link51 11 8 e) :=
  source_center_represented raw8 link51 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source51Center11Q8
