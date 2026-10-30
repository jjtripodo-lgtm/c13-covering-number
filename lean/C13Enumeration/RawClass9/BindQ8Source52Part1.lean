import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table8

namespace C13.Enumeration.RawClass9.Source52Center11Q8
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,3,2,5,1,6,7,4,9,10,11,8,12]
  invFun := ![0,4,2,1,7,3,5,6,11,8,9,10,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (11 : Point) = 8 := by decide +kernel
theorem star_image : transport normalizer (link link52 11) = link link09 8 := by decide +kernel

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
    (codedEmit CatalogCodes.codes52 11 8
      (fun x => Template8.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template8.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template8.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template8.maps.length = (((List.finRange Template8.maps.length).drop 0).take 16) := by decide +kernel
  rw [hsplit]
  exact chunk0_checked

theorem codes_checked : ∀ i : Fin Template8.maps.length,
    (raw8.pencil (table8.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes52 11 8
        (fun x => Template8.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw8 link52 11 8 normalizer Template8.maps :=
  mapsRepresented_of_code_checks raw8 table8 CatalogCodes.codes52
    link52 CatalogCodes.checked52 11 8 normalizer Template8.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 8) (hc : e (11 : Point) = hole)
    (hs : transport e (link link52 11) = link link09 8) :
    ∃ p ∈ raw8.supported.domain.2, RepresentsPencil p (emitPencil link52 11 8 e) :=
  source_center_represented raw8 link52 link09 hole 11 8 normalizer
    hole_fixed center_image star_image Template8.maps Template8.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source52Center11Q8
