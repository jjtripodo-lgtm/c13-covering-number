import C13Enumeration.RawClass9.CatalogCodes
import C13Enumeration.RawClass9.Table6

namespace C13.Enumeration.RawClass9.Source35Center09Q6
open C13.SourceData C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normalizer : Equiv.Perm Point where
  toFun := ![1,3,0,2,9,11,8,10,4,6,5,7,12]
  invFun := ![2,0,3,1,8,10,9,11,6,4,7,5,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : normalizer hole = hole := by decide +kernel
theorem center_image : normalizer (9 : Point) = 6 := by decide +kernel
theorem star_image : transport normalizer (link link35 9) = link link09 6 := by decide +kernel

def pick : Fin Template6.maps.length → table6.Index := ![
  ⟨⟨1,by decide +kernel⟩,⟨60,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨31,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨106,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨61,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨57,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨111,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨40,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨63,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨71,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨47,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨26,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨79,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨57,by decide +kernel⟩⟩,
  ⟨⟨17,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨102,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨26,by decide +kernel⟩,⟨124,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨127,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨42,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨34,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨21,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨76,by decide +kernel⟩⟩,
  ⟨⟨10,by decide +kernel⟩,⟨88,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨70,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨13,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨119,by decide +kernel⟩⟩,
  ⟨⟨21,by decide +kernel⟩,⟨118,by decide +kernel⟩⟩,
  ⟨⟨16,by decide +kernel⟩,⟨79,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨22,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨114,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨18,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨68,by decide +kernel⟩⟩,
  ⟨⟨8,by decide +kernel⟩,⟨53,by decide +kernel⟩⟩,
  ⟨⟨19,by decide +kernel⟩,⟨113,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨72,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨29,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨2,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨24,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨56,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨122,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨66,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨1,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨90,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨25,by decide +kernel⟩⟩,
  ⟨⟨12,by decide +kernel⟩,⟨11,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨58,by decide +kernel⟩⟩,
  ⟨⟨27,by decide +kernel⟩,⟨61,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨80,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨36,by decide +kernel⟩⟩,
  ⟨⟨5,by decide +kernel⟩,⟨127,by decide +kernel⟩⟩,
  ⟨⟨15,by decide +kernel⟩,⟨3,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨23,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨110,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨103,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨107,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨39,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨48,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨89,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨9,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩,
  ⟨⟨18,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩,
  ⟨⟨23,by decide +kernel⟩,⟨112,by decide +kernel⟩⟩,
  ⟨⟨6,by decide +kernel⟩,⟨76,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨117,by decide +kernel⟩⟩,
  ⟨⟨3,by decide +kernel⟩,⟨8,by decide +kernel⟩⟩,
  ⟨⟨14,by decide +kernel⟩,⟨50,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨6,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨99,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨88,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨35,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨38,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨20,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨98,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨46,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨116,by decide +kernel⟩⟩,
  ⟨⟨11,by decide +kernel⟩,⟨95,by decide +kernel⟩⟩,
  ⟨⟨22,by decide +kernel⟩,⟨10,by decide +kernel⟩⟩,
  ⟨⟨20,by decide +kernel⟩,⟨30,by decide +kernel⟩⟩,
  ⟨⟨7,by decide +kernel⟩,⟨33,by decide +kernel⟩⟩,
  ⟨⟨25,by decide +kernel⟩,⟨98,by decide +kernel⟩⟩,
  ⟨⟨13,by decide +kernel⟩,⟨97,by decide +kernel⟩⟩,
  ⟨⟨4,by decide +kernel⟩,⟨51,by decide +kernel⟩⟩,
  ⟨⟨1,by decide +kernel⟩,⟨115,by decide +kernel⟩⟩
]

def rowCheck (i : Fin Template6.maps.length) : Bool :=
  decide ((raw6.pencil (table6.row (pick i))).toFinset =
    (codedEmit CatalogCodes.codes35 9 6
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
      (codedEmit CatalogCodes.codes35 9 6
        (fun x => Template6.maps.get i (normalizer x))).toFinset := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp rows_checked) i (by simp))

theorem represented : MapsRepresented raw6 link35 9 6 normalizer Template6.maps :=
  mapsRepresented_of_code_checks raw6 table6 CatalogCodes.codes35
    link35 CatalogCodes.checked35 9 6 normalizer Template6.maps pick codes_checked

theorem complete (e : Equiv.Perm Point) (he : e hole = 6) (hc : e (9 : Point) = hole)
    (hs : transport e (link link35 9) = link link09 6) :
    ∃ p ∈ raw6.supported.domain.2, RepresentsPencil p (emitPencil link35 9 6 e) :=
  source_center_represented raw6 link35 link09 hole 9 6 normalizer
    hole_fixed center_image star_image Template6.maps Template6.complete represented e he hc hs
end C13.Enumeration.RawClass9.Source35Center09Q6
