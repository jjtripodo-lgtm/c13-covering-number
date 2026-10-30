import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table6

namespace C13.Enumeration.RawClass9.Source45Center06Q6
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![0,1,2,3,4,5,6,7,8,9,10,11,12]
  invFun := ![0,1,2,3,4,5,6,7,8,9,10,11,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (6 : Point) = 6 := by decide +kernel
theorem star_image : transport normalizer (link link45 6) = link link09 6 := by decide +kernel

def pick : Fin Template6.maps.length → table6.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨83,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨60,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨45,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨80,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨124,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨100,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨111,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨104,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨83,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨60,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨65,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨45,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨80,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨63,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨112,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨101,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨14,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨124,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨87,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨100,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨41,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨104,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨111,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨63,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨112,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨32,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨126,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨101,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨92,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨69,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨90,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨81,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨49,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨94,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨125,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨17,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨92,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨90,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨69,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨108,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨74,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨91,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨86,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩,
  ⟨⟨9,by decide +kernel⟩,⟨123,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨81,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨49,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨74,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨91,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨86,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨24,by decide +kernel⟩,⟨0,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template6.maps.length) : Bool :=
  decide ((raw6.pencil (table6.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes45 6 6
      (fun x => Template6.maps.get i (normalizer x))).toFinset)

theorem chunk0_checked : ((((List.finRange Template6.maps.length).drop 0).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk1_checked : ((((List.finRange Template6.maps.length).drop 16).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk2_checked : ((((List.finRange Template6.maps.length).drop 32).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk3_checked : ((((List.finRange Template6.maps.length).drop 48).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk4_checked : ((((List.finRange Template6.maps.length).drop 64).take 16).all rowCheck) = true := by
  decide +kernel

theorem chunk5_checked : ((((List.finRange Template6.maps.length).drop 80).take 16).all rowCheck) = true := by
  decide +kernel

theorem rows_checked : ((List.finRange Template6.maps.length).all rowCheck) = true := by
  have hsplit : List.finRange Template6.maps.length = (((List.finRange Template6.maps.length).drop 0).take 16) ++ (((List.finRange Template6.maps.length).drop 16).take 16) ++ (((List.finRange Template6.maps.length).drop 32).take 16) ++ (((List.finRange Template6.maps.length).drop 48).take 16) ++ (((List.finRange Template6.maps.length).drop 64).take 16) ++ (((List.finRange Template6.maps.length).drop 80).take 16) := by decide +kernel
  rw [hsplit]
  simp only [List.all_append,Bool.and_eq_true,and_assoc]
  exact ⟨chunk0_checked,chunk1_checked,chunk2_checked,chunk3_checked,chunk4_checked,chunk5_checked⟩

theorem codes_checked : ∀ i : Fin Template6.maps.length,
    (raw6.pencil (table6.row (pick i))).toFinset =
      (codedEmit CatalogCodes.codes45 6 6
        (fun x => Template6.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw6 link45 6 6 normalizer Template6.maps :=
  mapsRepresented_of_code_checks raw6 table6 CatalogCodes.codes45
    link45 CatalogCodes.checked45 6 6 normalizer Template6.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 6) (hc : e (6 : Point) = hole)
    (hs : transport e (link link45 6) = link link09 6) :
    ∃ p ∈ raw6.supported.domain.2, RepresentsPencil p (emitPencil link45 6 6 e) :=
  source_center_represented raw6 link45 link09 hole 6 6 normalizer
    hole_fixed center_image star_image Template6.maps Template6.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source45Center06Q6
