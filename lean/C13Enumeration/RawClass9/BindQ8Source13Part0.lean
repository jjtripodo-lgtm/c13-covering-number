import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source13Center02Q8
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
theorem star_image : transport normalizer (link link13 2) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨27,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨80,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨59,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨73,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨58,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨63,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨74,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨37,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨57,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨84,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes13 2 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes13 2 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link13 2 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes13
    link13 CatalogCodes.checked13 2 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (2 : Point) = hole)
    (hs : transport e (link link13 2) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link13 2 8 e) :=
  source_center_represented raw8 link13 link09 hole 2 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source13Center02Q8
namespace C13.Enumeration.RawClass9.Source13Center03Q8
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
theorem star_image : transport normalizer (link link13 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨27,by decide +kernel⟩,⟨57,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨84,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨58,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨63,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨74,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨37,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨59,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨73,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨80,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes13 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes13 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link13 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes13
    link13 CatalogCodes.checked13 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link13 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link13 3 8 e) :=
  source_center_represented raw8 link13 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source13Center03Q8
namespace C13.Enumeration.RawClass9.Source13Center06Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![5,2,4,3,9,10,8,11,0,7,1,6,12]
  invFun := ![8,10,1,3,2,0,11,9,6,4,5,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (6 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link13 6) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨26,by decide +kernel⟩,⟨118,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨124,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨45,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes13 6 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes13 6 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link13 6 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes13
    link13 CatalogCodes.checked13 6 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (6 : Point) = hole)
    (hs : transport e (link link13 6) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link13 6 8 e) :=
  source_center_represented raw8 link13 link09 hole 6 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source13Center06Q8
namespace C13.Enumeration.RawClass9.Source13Center07Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,5,3,4,10,9,11,8,0,7,1,6,12]
  invFun := ![8,10,0,2,3,1,11,9,7,5,4,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (7 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link13 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨26,by decide +kernel⟩,⟨118,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨124,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨45,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes13 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes13 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link13 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes13
    link13 CatalogCodes.checked13 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link13 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link13 7 8 e) :=
  source_center_represented raw8 link13 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source13Center07Q8
namespace C13.Enumeration.RawClass9.Source13Center09Q8
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
theorem star_image : transport normalizer (link link13 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨20,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨127,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨101,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨37,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨127,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨101,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨37,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes13 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes13 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link13 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes13
    link13 CatalogCodes.checked13 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link13 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link13 9 8 e) :=
  source_center_represented raw8 link13 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source13Center09Q8
namespace C13.Enumeration.RawClass9.Source13Center11Q8
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
theorem star_image : transport normalizer (link link13 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨20,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨12,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨112,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨12,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨112,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes13 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes13 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link13 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes13
    link13 CatalogCodes.checked13 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link13 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link13 11 8 e) :=
  source_center_represented raw8 link13 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source13Center11Q8
