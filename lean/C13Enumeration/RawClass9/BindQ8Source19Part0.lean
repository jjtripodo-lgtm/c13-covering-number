import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source19Center06Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,3,1,2,9,10,8,11,5,6,4,7,12]
  invFun := ![0,2,3,1,10,8,9,11,6,4,5,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (6 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link19 6) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes19 6 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes19 6 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link19 6 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes19
    link19 CatalogCodes.checked19 6 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (6 : Point) = hole)
    (hs : transport e (link link19 6) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link19 6 8 e) :=
  source_center_represented raw8 link19 link09 hole 6 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source19Center06Q8
namespace C13.Enumeration.RawClass9.Source19Center07Q8
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
theorem star_image : transport normalizer (link link19 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨121,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes19 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes19 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link19 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes19
    link19 CatalogCodes.checked19 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link19 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link19 7 8 e) :=
  source_center_represented raw8 link19 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source19Center07Q8
namespace C13.Enumeration.RawClass9.Source19Center08Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,0,3,1,6,4,7,5,8,10,9,11,12]
  invFun := ![1,3,0,2,5,7,4,6,8,10,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (8 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link19 8) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨104,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨98,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨105,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨110,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨104,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨109,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨45,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨99,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes19 8 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes19 8 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link19 8 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes19
    link19 CatalogCodes.checked19 8 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (8 : Point) = hole)
    (hs : transport e (link link19 8) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link19 8 8 e) :=
  source_center_represented raw8 link19 link09 hole 8 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source19Center08Q8
namespace C13.Enumeration.RawClass9.Source19Center09Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,0,3,1,4,6,5,7,10,8,11,9,12]
  invFun := ![1,3,0,2,4,6,5,7,9,11,8,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (9 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link19 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨104,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨98,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨105,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨110,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨104,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨109,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨45,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨99,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes19 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes19 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link19 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes19
    link19 CatalogCodes.checked19 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link19 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link19 9 8 e) :=
  source_center_represented raw8 link19 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source19Center09Q8
namespace C13.Enumeration.RawClass9.Source19Center10Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![3,0,2,1,6,5,7,4,9,10,8,11,12]
  invFun := ![1,3,2,0,7,5,4,6,10,8,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (10 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link19 10) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨109,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨45,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨99,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨110,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨104,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨105,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨104,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨98,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes19 10 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes19 10 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link19 10 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes19
    link19 CatalogCodes.checked19 10 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (10 : Point) = hole)
    (hs : transport e (link link19 10) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link19 10 8 e) :=
  source_center_represented raw8 link19 link09 hole 10 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source19Center10Q8
namespace C13.Enumeration.RawClass9.Source19Center11Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![3,0,2,1,5,6,4,7,10,9,11,8,12]
  invFun := ![1,3,2,0,6,4,5,7,11,9,8,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (11 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link19 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨109,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨45,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨120,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨99,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨110,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨104,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨105,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨104,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨98,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes19 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes19 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link19 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes19
    link19 CatalogCodes.checked19 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link19 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link19 11 8 e) :=
  source_center_represented raw8 link19 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source19Center11Q8
