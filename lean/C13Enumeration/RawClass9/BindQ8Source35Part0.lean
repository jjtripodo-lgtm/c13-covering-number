import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source35Center01Q8
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
theorem star_image : transport normalizer (link link35 1) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨2,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨88,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨82,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨66,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨107,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨110,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨61,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨86,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨105,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨44,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes35 1 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes35 1 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link35 1 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes35
    link35 CatalogCodes.checked35 1 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (1 : Point) = hole)
    (hs : transport e (link link35 1) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link35 1 8 e) :=
  source_center_represented raw8 link35 link09 hole 1 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source35Center01Q8
namespace C13.Enumeration.RawClass9.Source35Center03Q8
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
theorem star_image : transport normalizer (link link35 3) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨2,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨79,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨7,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨63,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨15,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨62,by decide +kernel⟩⟩,
  ⟨⟨2,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨80,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes35 3 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes35 3 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link35 3 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes35
    link35 CatalogCodes.checked35 3 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (3 : Point) = hole)
    (hs : transport e (link link35 3) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link35 3 8 e) :=
  source_center_represented raw8 link35 link09 hole 3 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source35Center03Q8
namespace C13.Enumeration.RawClass9.Source35Center06Q8
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
theorem star_image : transport normalizer (link link35 6) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨12,by decide +kernel⟩,⟨57,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨100,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨88,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨37,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨80,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨68,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨127,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨52,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨19,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨90,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes35 6 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes35 6 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link35 6 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes35
    link35 CatalogCodes.checked35 6 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (6 : Point) = hole)
    (hs : transport e (link link35 6) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link35 6 8 e) :=
  source_center_represented raw8 link35 link09 hole 6 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source35Center06Q8
namespace C13.Enumeration.RawClass9.Source35Center10Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![2,5,0,3,4,7,6,1,10,9,8,11,12]
  invFun := ![2,7,0,3,4,1,6,5,10,9,8,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (10 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link35 10) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨11,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨111,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨57,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨16,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨110,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨54,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨28,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨96,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨127,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨85,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨101,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨55,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes35 10 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes35 10 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link35 10 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes35
    link35 CatalogCodes.checked35 10 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (10 : Point) = hole)
    (hs : transport e (link link35 10) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link35 10 8 e) :=
  source_center_represented raw8 link35 link09 hole 10 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source35Center10Q8
namespace C13.Enumeration.RawClass9.Source35Center11Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![5,2,0,3,7,4,6,1,10,9,11,8,12]
  invFun := ![2,7,1,3,5,0,6,4,11,9,8,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (11 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link35 11) = link link09 8 := by decide +kernel

def pick : Fin Template8.maps.length → table8.Index := ![
  ⟨⟨12,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨67,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨60,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨45,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨93,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨77,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨55,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨82,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template8.maps.length) : Bool :=
  decide ((raw8.pencil (table8.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes35 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes35 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link35 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes35
    link35 CatalogCodes.checked35 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link35 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link35 11 8 e) :=
  source_center_represented raw8 link35 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source35Center11Q8
