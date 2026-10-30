import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source05Center06Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,1,2,3,10,11,8,9,6,7,4,5,12]
  invFun := ![0,1,2,3,10,11,8,9,6,7,4,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (6 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link05 6) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes05 6 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes05 6 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link05 6 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes05
    link05 CatalogCodes.checked05 6 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (6 : Point) = hole)
    (hs : transport e (link link05 6) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link05 6 8 e) :=
  source_center_represented raw8 link05 link09 hole 6 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source05Center06Q8
namespace C13.Enumeration.RawClass9.Source05Center07Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,1,3,2,10,11,9,8,6,7,5,4,12]
  invFun := ![0,1,3,2,11,10,8,9,7,6,4,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (7 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link05 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes05 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes05 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link05 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes05
    link05 CatalogCodes.checked05 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link05 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link05 7 8 e) :=
  source_center_represented raw8 link05 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source05Center07Q8
namespace C13.Enumeration.RawClass9.Source05Center08Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,3,0,1,6,7,4,5,8,9,10,11,12]
  invFun := ![2,3,0,1,6,7,4,5,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (8 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link05 8) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes05 8 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes05 8 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link05 8 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes05
    link05 CatalogCodes.checked05 8 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (8 : Point) = hole)
    (hs : transport e (link link05 8) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link05 8 8 e) :=
  source_center_represented raw8 link05 link09 hole 8 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source05Center08Q8
namespace C13.Enumeration.RawClass9.Source05Center09Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![3,2,0,1,6,7,5,4,9,8,10,11,12]
  invFun := ![2,3,1,0,7,6,4,5,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (9 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link05 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes05 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes05 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link05 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes05
    link05 CatalogCodes.checked05 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link05 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link05 9 8 e) :=
  source_center_represented raw8 link05 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source05Center09Q8
namespace C13.Enumeration.RawClass9.Source05Center10Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  invFun := ![2,3,0,1,4,5,6,7,10,11,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (10 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link05 10) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨40,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨40,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨40,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨40,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes05 10 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes05 10 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link05 10 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes05
    link05 CatalogCodes.checked05 10 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (10 : Point) = hole)
    (hs : transport e (link link05 10) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link05 10 8 e) :=
  source_center_represented raw8 link05 link09 hole 10 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source05Center10Q8
namespace C13.Enumeration.RawClass9.Source05Center11Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![3,2,0,1,5,4,6,7,10,11,9,8,12]
  invFun := ![2,3,1,0,5,4,6,7,11,10,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (11 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link05 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨40,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨40,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨40,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨40,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes05 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes05 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link05 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes05
    link05 CatalogCodes.checked05 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link05 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link05 11 8 e) :=
  source_center_represented raw8 link05 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source05Center11Q8
