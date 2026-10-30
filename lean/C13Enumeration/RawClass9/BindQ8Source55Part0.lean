import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source55Center02Q8
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
theorem star_image : transport normalizer (link link55 2) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨12,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨64,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨85,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨73,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes55 2 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes55 2 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link55 2 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes55
    link55 CatalogCodes.checked55 2 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (2 : Point) = hole)
    (hs : transport e (link link55 2) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link55 2 8 e) :=
  source_center_represented raw8 link55 link09 hole 2 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source55Center02Q8
namespace C13.Enumeration.RawClass9.Source55Center03Q8
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
theorem star_image : transport normalizer (link link55 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨49,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨107,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨92,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨69,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨101,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨37,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes55 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes55 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link55 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes55
    link55 CatalogCodes.checked55 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link55 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link55 3 8 e) :=
  source_center_represented raw8 link55 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source55Center03Q8
namespace C13.Enumeration.RawClass9.Source55Center05Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,5,3,2,9,8,10,11,1,4,6,7,12]
  invFun := ![0,8,3,2,9,1,10,11,5,4,6,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (5 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link55 5) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨12,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨64,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨85,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨73,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes55 5 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes55 5 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link55 5 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes55
    link55 CatalogCodes.checked55 5 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (5 : Point) = hole)
    (hs : transport e (link link55 5) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link55 5 8 e) :=
  source_center_represented raw8 link55 link09 hole 5 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source55Center05Q8
namespace C13.Enumeration.RawClass9.Source55Center07Q8
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
theorem star_image : transport normalizer (link link55 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨107,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨92,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨49,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨69,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨101,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨37,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes55 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes55 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link55 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes55
    link55 CatalogCodes.checked55 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link55 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link55 7 8 e) :=
  source_center_represented raw8 link55 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source55Center07Q8
namespace C13.Enumeration.RawClass9.Source55Center09Q8
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
theorem star_image : transport normalizer (link link55 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨118,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨59,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨127,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨80,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨99,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes55 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes55 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link55 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes55
    link55 CatalogCodes.checked55 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link55 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link55 9 8 e) :=
  source_center_represented raw8 link55 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source55Center09Q8
namespace C13.Enumeration.RawClass9.Source55Center10Q8
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
theorem star_image : transport normalizer (link link55 10) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨12,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨127,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨99,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨80,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨118,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨59,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes55 10 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes55 10 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link55 10 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes55
    link55 CatalogCodes.checked55 10 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (10 : Point) = hole)
    (hs : transport e (link link55 10) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link55 10 8 e) :=
  source_center_represented raw8 link55 link09 hole 10 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source55Center10Q8
