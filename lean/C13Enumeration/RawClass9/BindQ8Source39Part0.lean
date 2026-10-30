import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source39Center01Q8
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
theorem star_image : transport normalizer (link link39 1) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨111,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨46,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨112,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨111,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨46,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨112,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨127,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨109,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨127,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨109,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes39 1 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes39 1 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link39 1 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes39
    link39 CatalogCodes.checked39 1 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (1 : Point) = hole)
    (hs : transport e (link link39 1) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link39 1 8 e) :=
  source_center_represented raw8 link39 link09 hole 1 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source39Center01Q8
namespace C13.Enumeration.RawClass9.Source39Center02Q8
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
theorem star_image : transport normalizer (link link39 2) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨101,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨107,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨124,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes39 2 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes39 2 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link39 2 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes39
    link39 CatalogCodes.checked39 2 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (2 : Point) = hole)
    (hs : transport e (link link39 2) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link39 2 8 e) :=
  source_center_represented raw8 link39 link09 hole 2 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source39Center02Q8
namespace C13.Enumeration.RawClass9.Source39Center03Q8
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
theorem star_image : transport normalizer (link link39 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨101,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨107,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨124,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes39 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes39 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link39 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes39
    link39 CatalogCodes.checked39 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link39 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link39 3 8 e) :=
  source_center_represented raw8 link39 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source39Center03Q8
namespace C13.Enumeration.RawClass9.Source39Center09Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,3,5,4,7,6,0,1,9,8,10,11,12]
  invFun := ![6,7,0,1,3,2,5,4,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (9 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link39 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨25,by decide +kernel⟩,⟨100,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨49,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨105,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨37,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨118,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨105,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨37,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨118,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨100,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨49,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes39 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes39 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link39 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes39
    link39 CatalogCodes.checked39 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link39 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link39 9 8 e) :=
  source_center_represented raw8 link39 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source39Center09Q8
namespace C13.Enumeration.RawClass9.Source39Center10Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![4,5,2,3,6,7,0,1,10,11,8,9,12]
  invFun := ![6,7,2,3,0,1,4,5,10,11,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (10 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link39 10) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨25,by decide +kernel⟩,⟨110,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨43,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨107,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨111,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨44,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨113,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨112,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨113,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes39 10 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes39 10 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link39 10 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes39
    link39 CatalogCodes.checked39 10 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (10 : Point) = hole)
    (hs : transport e (link link39 10) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link39 10 8 e) :=
  source_center_represented raw8 link39 link09 hole 10 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source39Center10Q8
namespace C13.Enumeration.RawClass9.Source39Center11Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![5,4,2,3,7,6,0,1,10,11,9,8,12]
  invFun := ![6,7,2,3,1,0,5,4,11,10,8,9,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (11 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link39 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨25,by decide +kernel⟩,⟨113,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨4,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨112,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨5,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨113,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨110,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨43,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨107,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨111,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨44,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes39 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes39 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link39 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes39
    link39 CatalogCodes.checked39 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link39 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link39 11 8 e) :=
  source_center_represented raw8 link39 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source39Center11Q8
