import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source58Center02Q8
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
theorem star_image : transport normalizer (link link58 2) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨76,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨82,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes58 2 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes58 2 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link58 2 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes58
    link58 CatalogCodes.checked58 2 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (2 : Point) = hole)
    (hs : transport e (link link58 2) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link58 2 8 e) :=
  source_center_represented raw8 link58 link09 hole 2 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source58Center02Q8
namespace C13.Enumeration.RawClass9.Source58Center03Q8
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
theorem star_image : transport normalizer (link link58 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨76,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨82,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes58 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes58 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link58 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes58
    link58 CatalogCodes.checked58 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link58 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link58 3 8 e) :=
  source_center_represented raw8 link58 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source58Center03Q8
namespace C13.Enumeration.RawClass9.Source58Center06Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,3,2,5,10,9,8,11,6,1,4,7,12]
  invFun := ![0,9,2,1,10,3,8,11,6,5,4,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (6 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link58 6) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨76,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨82,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes58 6 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes58 6 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link58 6 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes58
    link58 CatalogCodes.checked58 6 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (6 : Point) = hole)
    (hs : transport e (link link58 6) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link58 6 8 e) :=
  source_center_represented raw8 link58 link09 hole 6 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source58Center06Q8
namespace C13.Enumeration.RawClass9.Source58Center07Q8
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
theorem star_image : transport normalizer (link link58 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨76,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨82,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes58 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes58 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link58 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes58
    link58 CatalogCodes.checked58 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link58 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link58 7 8 e) :=
  source_center_represented raw8 link58 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source58Center07Q8
namespace C13.Enumeration.RawClass9.Source58Center10Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![3,0,2,5,6,1,7,4,9,10,8,11,12]
  invFun := ![1,5,2,0,7,3,4,6,10,8,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (10 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link58 10) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨76,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨82,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes58 10 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes58 10 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link58 10 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes58
    link58 CatalogCodes.checked58 10 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (10 : Point) = hole)
    (hs : transport e (link link58 10) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link58 10 8 e) :=
  source_center_represented raw8 link58 link09 hole 10 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source58Center10Q8
namespace C13.Enumeration.RawClass9.Source58Center11Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![3,0,5,2,6,1,4,7,9,10,11,8,12]
  invFun := ![1,5,3,0,6,2,4,7,11,8,9,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (11 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link58 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨76,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨82,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes58 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes58 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link58 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes58
    link58 CatalogCodes.checked58 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link58 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link58 11 8 e) :=
  source_center_represented raw8 link58 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source58Center11Q8
