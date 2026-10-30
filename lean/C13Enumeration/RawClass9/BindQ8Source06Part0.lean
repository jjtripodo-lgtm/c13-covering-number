import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source06Center03Q8
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
theorem star_image : transport normalizer (link link06 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨5,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨73,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨73,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes06 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes06 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link06 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes06
    link06 CatalogCodes.checked06 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link06 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link06 3 8 e) :=
  source_center_represented raw8 link06 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source06Center03Q8
namespace C13.Enumeration.RawClass9.Source06Center07Q8
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
theorem star_image : transport normalizer (link link06 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨5,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨73,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨73,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes06 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes06 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link06 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes06
    link06 CatalogCodes.checked06 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link06 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link06 7 8 e) :=
  source_center_represented raw8 link06 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source06Center07Q8
namespace C13.Enumeration.RawClass9.Source06Center09Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![3,2,0,5,6,7,1,4,9,8,10,11,12]
  invFun := ![2,6,1,0,7,3,4,5,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (9 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link06 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨10,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨75,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes06 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes06 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link06 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes06
    link06 CatalogCodes.checked06 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link06 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link06 9 8 e) :=
  source_center_represented raw8 link06 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source06Center09Q8
namespace C13.Enumeration.RawClass9.Source06Center10Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![5,2,0,3,4,7,1,6,9,10,8,11,12]
  invFun := ![2,6,1,3,4,0,7,5,10,8,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (10 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link06 10) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨10,by decide +kernel⟩,⟨92,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨80,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨98,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨80,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨92,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨98,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes06 10 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes06 10 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link06 10 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes06
    link06 CatalogCodes.checked06 10 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (10 : Point) = hole)
    (hs : transport e (link link06 10) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link06 10 8 e) :=
  source_center_represented raw8 link06 link09 hole 10 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source06Center10Q8
namespace C13.Enumeration.RawClass9.Source06Center11Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,5,0,3,7,4,1,6,9,10,11,8,12]
  invFun := ![2,6,0,3,5,1,7,4,11,8,9,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (11 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link06 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨10,by decide +kernel⟩,⟨92,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨80,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨98,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨80,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨92,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨98,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes06 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes06 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link06 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes06
    link06 CatalogCodes.checked06 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link06 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link06 11 8 e) :=
  source_center_represented raw8 link06 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source06Center11Q8
