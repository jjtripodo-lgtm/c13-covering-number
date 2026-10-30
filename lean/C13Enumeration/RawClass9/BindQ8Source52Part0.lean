import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source52Center01Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![9,8,10,11,0,5,3,2,1,4,6,7,12]
  invFun := ![4,8,7,6,9,5,10,11,1,0,2,3,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (1 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link52 1) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes52 1 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes52 1 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link52 1 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes52
    link52 CatalogCodes.checked52 1 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (1 : Point) = hole)
    (hs : transport e (link link52 1) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link52 1 8 e) :=
  source_center_represented raw8 link52 link09 hole 1 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source52Center01Q8
namespace C13.Enumeration.RawClass9.Source52Center02Q8
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
theorem star_image : transport normalizer (link link52 2) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes52 2 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes52 2 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link52 2 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes52
    link52 CatalogCodes.checked52 2 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (2 : Point) = hole)
    (hs : transport e (link link52 2) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link52 2 8 e) :=
  source_center_represented raw8 link52 link09 hole 2 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source52Center02Q8
namespace C13.Enumeration.RawClass9.Source52Center03Q8
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
theorem star_image : transport normalizer (link link52 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes52 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes52 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link52 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes52
    link52 CatalogCodes.checked52 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link52 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link52 3 8 e) :=
  source_center_represented raw8 link52 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source52Center03Q8
namespace C13.Enumeration.RawClass9.Source52Center05Q8
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
theorem star_image : transport normalizer (link link52 5) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes52 5 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes52 5 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link52 5 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes52
    link52 CatalogCodes.checked52 5 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (5 : Point) = hole)
    (hs : transport e (link link52 5) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link52 5 8 e) :=
  source_center_represented raw8 link52 link09 hole 5 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source52Center05Q8
namespace C13.Enumeration.RawClass9.Source52Center06Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,3,5,2,9,10,8,11,1,6,4,7,12]
  invFun := ![0,8,3,1,10,2,9,11,6,4,5,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (6 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link52 6) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes52 6 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes52 6 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link52 6 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes52
    link52 CatalogCodes.checked52 6 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (6 : Point) = hole)
    (hs : transport e (link link52 6) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link52 6 8 e) :=
  source_center_represented raw8 link52 link09 hole 6 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source52Center06Q8
namespace C13.Enumeration.RawClass9.Source52Center07Q8
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
theorem star_image : transport normalizer (link link52 7) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes52 7 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes52 7 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link52 7 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes52
    link52 CatalogCodes.checked52 7 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (7 : Point) = hole)
    (hs : transport e (link link52 7) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link52 7 8 e) :=
  source_center_represented raw8 link52 link09 hole 7 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source52Center07Q8
namespace C13.Enumeration.RawClass9.Source52Center09Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,5,3,2,1,4,6,7,9,8,10,11,12]
  invFun := ![0,4,3,2,5,1,6,7,9,8,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (9 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link52 9) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes52 9 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes52 9 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link52 9 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes52
    link52 CatalogCodes.checked52 9 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (9 : Point) = hole)
    (hs : transport e (link link52 9) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link52 9 8 e) :=
  source_center_represented raw8 link52 link09 hole 9 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source52Center09Q8
namespace C13.Enumeration.RawClass9.Source52Center10Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,3,5,2,1,6,4,7,9,10,8,11,12]
  invFun := ![0,4,3,1,6,2,5,7,10,8,9,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (10 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link52 10) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes52 10 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes52 10 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link52 10 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes52
    link52 CatalogCodes.checked52 10 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (10 : Point) = hole)
    (hs : transport e (link link52 10) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link52 10 8 e) :=
  source_center_represented raw8 link52 link09 hole 10 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source52Center10Q8
