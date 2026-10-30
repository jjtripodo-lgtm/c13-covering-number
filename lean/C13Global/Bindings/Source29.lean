import C13Global.RecordBinding
import C13Global.Data.Source29
namespace C13.Global.Source29
open C13.SourceData C13.Checker.RawSupport C13.Enumeration C13.Enumeration.Canonical
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem root_binding : decodeSource rootCodes = link29 := by decide +kernel

theorem nonincident_checked : (List.finRange 13).all (fun q => if q = hole then true else
  decide ((nonincidentAt q).mask &&& alphabets.getD q.val 0 = (nonincidentAt q).mask)) = true := by decide +kernel

theorem nonincident_complete : NonincidentComplete alphabets := nonincident_complete_of_check alphabets nonincident_checked

theorem alphabet_checked00 : (relabelDomain (domains 19) Normalizers.Source29.normalizer00.symm 0).alphabet.all
    (fun b => (alphabets.getD 0 0).testBit b.toNat) = true := by decide +kernel

theorem alphabet_checked01 : (relabelDomain (domains 8) Normalizers.Source29.normalizer01.symm 1).alphabet.all
    (fun b => (alphabets.getD 1 0).testBit b.toNat) = true := by decide +kernel

theorem alphabet_checked02 : (relabelDomain (domains 1) Normalizers.Source29.normalizer02.symm 2).alphabet.all
    (fun b => (alphabets.getD 2 0).testBit b.toNat) = true := by decide +kernel

theorem alphabet_checked03 : (relabelDomain (domains 1) Normalizers.Source29.normalizer03.symm 3).alphabet.all
    (fun b => (alphabets.getD 3 0).testBit b.toNat) = true := by decide +kernel

theorem alphabet_checked04 : (relabelDomain (domains 32) Normalizers.Source29.normalizer04.symm 4).alphabet.all
    (fun b => (alphabets.getD 4 0).testBit b.toNat) = true := by decide +kernel

theorem alphabet_checked05 : (relabelDomain (domains 15) Normalizers.Source29.normalizer05.symm 5).alphabet.all
    (fun b => (alphabets.getD 5 0).testBit b.toNat) = true := by decide +kernel

theorem alphabet_checked06 : (relabelDomain (domains 1) Normalizers.Source29.normalizer06.symm 6).alphabet.all
    (fun b => (alphabets.getD 6 0).testBit b.toNat) = true := by decide +kernel

theorem alphabet_checked07 : (relabelDomain (domains 1) Normalizers.Source29.normalizer07.symm 7).alphabet.all
    (fun b => (alphabets.getD 7 0).testBit b.toNat) = true := by decide +kernel

theorem alphabet_checked08 : (relabelDomain (domains 8) Normalizers.Source29.normalizer08.symm 8).alphabet.all
    (fun b => (alphabets.getD 8 0).testBit b.toNat) = true := by decide +kernel

theorem alphabet_checked09 : (relabelDomain (domains 6) Normalizers.Source29.normalizer09.symm 9).alphabet.all
    (fun b => (alphabets.getD 9 0).testBit b.toNat) = true := by decide +kernel

theorem alphabet_checked10 : (relabelDomain (domains 1) Normalizers.Source29.normalizer10.symm 10).alphabet.all
    (fun b => (alphabets.getD 10 0).testBit b.toNat) = true := by decide +kernel

theorem alphabet_checked11 : (relabelDomain (domains 1) Normalizers.Source29.normalizer11.symm 11).alphabet.all
    (fun b => (alphabets.getD 11 0).testBit b.toNat) = true := by decide +kernel

theorem alphabet_complete : AlphabetComplete link29 alphabets := by
  intro q hq P hp B hB
  fin_cases q
  · exact record_alphabet_complete Normalizers.Source29.record00 _ alphabet_checked00 P hp B hB
  · exact record_alphabet_complete Normalizers.Source29.record01 _ alphabet_checked01 P hp B hB
  · exact record_alphabet_complete Normalizers.Source29.record02 _ alphabet_checked02 P hp B hB
  · exact record_alphabet_complete Normalizers.Source29.record03 _ alphabet_checked03 P hp B hB
  · exact record_alphabet_complete Normalizers.Source29.record04 _ alphabet_checked04 P hp B hB
  · exact record_alphabet_complete Normalizers.Source29.record05 _ alphabet_checked05 P hp B hB
  · exact record_alphabet_complete Normalizers.Source29.record06 _ alphabet_checked06 P hp B hB
  · exact record_alphabet_complete Normalizers.Source29.record07 _ alphabet_checked07 P hp B hB
  · exact record_alphabet_complete Normalizers.Source29.record08 _ alphabet_checked08 P hp B hB
  · exact record_alphabet_complete Normalizers.Source29.record09 _ alphabet_checked09 P hp B hB
  · exact record_alphabet_complete Normalizers.Source29.record10 _ alphabet_checked10 P hp B hB
  · exact record_alphabet_complete Normalizers.Source29.record11 _ alphabet_checked11 P hp B hB
  · exact (hq rfl).elim

theorem empty_obstruction (c : EmptyCase) (hc : c ∈ emptyCases)
    (hclass : C13.ClassifiesMinimumLinks catalog hole)
    (F : C13.Family C13.Point) (hcover : C13.IsCoverOn Finset.univ F 7 4)
    (hroot : C13.link F hole = link29)
    (hpoints : ∀ q ∈ c.1, q ≠ hole) (hmin : ∀ q ∈ c.1, C13.degree F q = 15) : False :=
  empty_actual_obstruction link29 rootCodes root_binding alphabets alphabet_complete
    nonincident_complete c (List.all_eq_true.mp empty_checked c hc)
    hclass F hcover hroot hpoints hmin

end C13.Global.Source29
