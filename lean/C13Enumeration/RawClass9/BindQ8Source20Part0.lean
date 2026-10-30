import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source20Center03Q8
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
theorem star_image : transport normalizer (link link20 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨5,by decide +kernel⟩,⟨92,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨113,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨113,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes20 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes20 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link20 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes20
    link20 CatalogCodes.checked20 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link20 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link20 3 8 e) :=
  source_center_represented raw8 link20 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source20Center03Q8
namespace C13.Enumeration.RawClass9.Source20Center07Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,3,1,2,10,9,11,8,6,5,7,4,12]
  invFun := ![0,2,3,1,11,9,8,10,7,5,4,6,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (7 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link20 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨5,by decide +kernel⟩,⟨92,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨113,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨113,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes20 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes20 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link20 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes20
    link20 CatalogCodes.checked20 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link20 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link20 7 8 e) :=
  source_center_represented raw8 link20 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source20Center07Q8
namespace C13.Enumeration.RawClass9.Source20Center08Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,0,5,3,6,4,1,7,8,10,11,9,12]
  invFun := ![1,6,0,3,5,2,4,7,8,11,9,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (8 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link20 8) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨10,by decide +kernel⟩,⟨91,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨91,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes20 8 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes20 8 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link20 8 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes20
    link20 CatalogCodes.checked20 8 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (8 : Point) = hole)
    (hs : transport e (link link20 8) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link20 8 8 e) :=
  source_center_represented raw8 link20 link09 hole 8 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source20Center08Q8
namespace C13.Enumeration.RawClass9.Source20Center09Q8
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
theorem star_image : transport normalizer (link link20 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨10,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨74,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨98,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨124,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨69,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨99,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨76,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨49,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨96,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes20 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes20 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link20 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes20
    link20 CatalogCodes.checked20 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link20 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link20 9 8 e) :=
  source_center_represented raw8 link20 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source20Center09Q8
namespace C13.Enumeration.RawClass9.Source20Center10Q8
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
theorem star_image : transport normalizer (link link20 10) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨99,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨96,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨76,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨49,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨98,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨74,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨124,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨69,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes20 10 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes20 10 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link20 10 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes20
    link20 CatalogCodes.checked20 10 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (10 : Point) = hole)
    (hs : transport e (link link20 10) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link20 10 8 e) :=
  source_center_represented raw8 link20 link09 hole 10 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source20Center10Q8
