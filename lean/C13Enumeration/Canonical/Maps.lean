import Mathlib.Tactic.FinCases
import C13Enumeration.Canonical.Pair00_00.Complete
import C13Enumeration.Canonical.Pair03_03.Complete
import C13Enumeration.Canonical.Pair04_04.Complete
import C13Enumeration.Canonical.Pair05_05.Complete
import C13Enumeration.Canonical.Pair07_07.Complete
import C13Enumeration.Canonical.Pair08_08.Complete
import C13Enumeration.Canonical.Pair09_09.Complete
import C13Enumeration.Canonical.Pair10_10.Complete
import C13Enumeration.Canonical.Pair11_11.Complete
import C13Enumeration.Canonical.Pair12_12.Complete
import C13Enumeration.Canonical.Pair13_13.Complete
import C13Enumeration.Canonical.Pair14_14.Complete
import C13Enumeration.Canonical.Pair15_15.Complete
import C13Enumeration.Canonical.Pair16_16.Complete
import C13Enumeration.Canonical.Pair17_17.Complete
import C13Enumeration.Canonical.Pair18_18.Complete
import C13Enumeration.Canonical.Pair19_19.Complete
import C13Enumeration.Canonical.Pair20_20.Complete
import C13Enumeration.Canonical.Pair21_21.Complete
import C13Enumeration.Canonical.Pair22_22.Complete
import C13Enumeration.Canonical.Pair23_23.Complete
import C13Enumeration.Canonical.Pair24_24.Complete
import C13Enumeration.Canonical.Pair25_25.Complete
import C13Enumeration.Canonical.Pair26_26.Complete
import C13Enumeration.Canonical.Pair27_27.Complete
import C13Enumeration.Canonical.Pair28_28.Complete
import C13Enumeration.Canonical.Pair29_29.Complete
import C13Enumeration.Canonical.Pair30_30.Complete
import C13Enumeration.Canonical.Pair31_31.Complete
import C13Enumeration.Canonical.Pair32_32.Complete
import C13Enumeration.Canonical.Pair33_33.Complete
import C13Enumeration.Canonical.Pair34_34.Complete
import C13Enumeration.Canonical.Pair35_35.Complete
import C13Enumeration.Canonical.Pair36_36.Complete
import C13Enumeration.Canonical.Pair37_37.Complete
import C13Enumeration.Canonical.Pair38_38.Complete
import C13Enumeration.Canonical.Pair39_39.Complete
import C13Enumeration.Canonical.Pair40_40.Complete
import C13Enumeration.Canonical.Pair41_41.Complete
import C13Enumeration.Canonical.Pair42_42.Complete
import C13Enumeration.Canonical.Pair43_43.Complete
import C13Enumeration.Canonical.Pair44_44.Complete
import C13Enumeration.Canonical.Pair45_45.Complete
import C13Enumeration.Canonical.Pair46_46.Complete
import C13Enumeration.Canonical.Pair47_47.Complete
import C13Enumeration.Canonical.Pair48_48.Complete
import C13Enumeration.Canonical.Pair49_49.Complete
import C13Enumeration.Canonical.Pair50_50.Complete
import C13Enumeration.Canonical.Pair51_51.Complete
import C13Enumeration.Canonical.Pair52_52.Complete
import C13Enumeration.Canonical.Pair53_53.Complete
import C13Enumeration.Canonical.Pair54_54.Complete
import C13Enumeration.Canonical.Pair55_55.Complete
import C13Enumeration.Canonical.Pair56_56.Complete
import C13Enumeration.Canonical.Pair57_57.Complete
import C13Enumeration.Canonical.Pair58_58.Complete
import C13Enumeration.Canonical.Pair59_59.Complete
import C13Enumeration.Canonical.Pair60_60.Complete
import C13Enumeration.Canonical.Pair61_61.Complete
import C13Enumeration.Template6.Complete
import C13Enumeration.Template8.Complete
import C13Enumeration.DegreeEightPilot.Source01Center04
namespace C13.Enumeration.Canonical
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def maps : Fin 62 → List (Point → Point) := ![Pair00_00.maps,Template8.maps,DegreeEightPilot.Source01Center04.maps,Pair03_03.maps,Pair04_04.maps,Pair05_05.maps,Template6.maps,Pair07_07.maps,Pair08_08.maps,Pair09_09.maps,Pair10_10.maps,Pair11_11.maps,Pair12_12.maps,Pair13_13.maps,Pair14_14.maps,Pair15_15.maps,Pair16_16.maps,Pair17_17.maps,Pair18_18.maps,Pair19_19.maps,Pair20_20.maps,Pair21_21.maps,Pair22_22.maps,Pair23_23.maps,Pair24_24.maps,Pair25_25.maps,Pair26_26.maps,Pair27_27.maps,Pair28_28.maps,Pair29_29.maps,Pair30_30.maps,Pair31_31.maps,Pair32_32.maps,Pair33_33.maps,Pair34_34.maps,Pair35_35.maps,Pair36_36.maps,Pair37_37.maps,Pair38_38.maps,Pair39_39.maps,Pair40_40.maps,Pair41_41.maps,Pair42_42.maps,Pair43_43.maps,Pair44_44.maps,Pair45_45.maps,Pair46_46.maps,Pair47_47.maps,Pair48_48.maps,Pair49_49.maps,Pair50_50.maps,Pair51_51.maps,Pair52_52.maps,Pair53_53.maps,Pair54_54.maps,Pair55_55.maps,Pair56_56.maps,Pair57_57.maps,Pair58_58.maps,Pair59_59.maps,Pair60_60.maps,Pair61_61.maps]

theorem maps_complete (i : Fin 62) (e : Equiv.Perm Point)
    (he : e hole = (templates i).center) (hc : e (templates i).center = hole)
    (hs : transport e (templates i).star = (templates i).star) : (e : Point → Point) ∈ maps i := by
  fin_cases i
  · exact Pair00_00.complete e he hc hs
  · exact Template8.complete e he hc hs
  · exact DegreeEightPilot.Source01Center04.complete_maps e he hc hs
  · exact Pair03_03.complete e he hc hs
  · exact Pair04_04.complete e he hc hs
  · exact Pair05_05.complete e he hc hs
  · exact Template6.complete e he hc hs
  · exact Pair07_07.complete e he hc hs
  · exact Pair08_08.complete e he hc hs
  · exact Pair09_09.complete e he hc hs
  · exact Pair10_10.complete e he hc hs
  · exact Pair11_11.complete e he hc hs
  · exact Pair12_12.complete e he hc hs
  · exact Pair13_13.complete e he hc hs
  · exact Pair14_14.complete e he hc hs
  · exact Pair15_15.complete e he hc hs
  · exact Pair16_16.complete e he hc hs
  · exact Pair17_17.complete e he hc hs
  · exact Pair18_18.complete e he hc hs
  · exact Pair19_19.complete e he hc hs
  · exact Pair20_20.complete e he hc hs
  · exact Pair21_21.complete e he hc hs
  · exact Pair22_22.complete e he hc hs
  · exact Pair23_23.complete e he hc hs
  · exact Pair24_24.complete e he hc hs
  · exact Pair25_25.complete e he hc hs
  · exact Pair26_26.complete e he hc hs
  · exact Pair27_27.complete e he hc hs
  · exact Pair28_28.complete e he hc hs
  · exact Pair29_29.complete e he hc hs
  · exact Pair30_30.complete e he hc hs
  · exact Pair31_31.complete e he hc hs
  · exact Pair32_32.complete e he hc hs
  · exact Pair33_33.complete e he hc hs
  · exact Pair34_34.complete e he hc hs
  · exact Pair35_35.complete e he hc hs
  · exact Pair36_36.complete e he hc hs
  · exact Pair37_37.complete e he hc hs
  · exact Pair38_38.complete e he hc hs
  · exact Pair39_39.complete e he hc hs
  · exact Pair40_40.complete e he hc hs
  · exact Pair41_41.complete e he hc hs
  · exact Pair42_42.complete e he hc hs
  · exact Pair43_43.complete e he hc hs
  · exact Pair44_44.complete e he hc hs
  · exact Pair45_45.complete e he hc hs
  · exact Pair46_46.complete e he hc hs
  · exact Pair47_47.complete e he hc hs
  · exact Pair48_48.complete e he hc hs
  · exact Pair49_49.complete e he hc hs
  · exact Pair50_50.complete e he hc hs
  · exact Pair51_51.complete e he hc hs
  · exact Pair52_52.complete e he hc hs
  · exact Pair53_53.complete e he hc hs
  · exact Pair54_54.complete e he hc hs
  · exact Pair55_55.complete e he hc hs
  · exact Pair56_56.complete e he hc hs
  · exact Pair57_57.complete e he hc hs
  · exact Pair58_58.complete e he hc hs
  · exact Pair59_59.complete e he hc hs
  · exact Pair60_60.complete e he hc hs
  · exact Pair61_61.complete e he hc hs

theorem maps_sound (i : Fin 62) : ∀ f ∈ maps i,
    GoodMap (templates i).family (templates i).family hole (templates i).center hole (templates i).center f := by
  fin_cases i
  · exact Pair00_00.every_listed_map_valid
  · exact Template8.every_listed_map_valid
  · intro f hf
    have h : (DegreeEightPilot.Source01Center04.maps.all fun g => decide (GoodMap link01 link01 hole 4 hole 4 g)) = true := by decide +kernel
    exact of_decide_eq_true ((List.all_eq_true.mp h) f hf)
  · exact Pair03_03.every_listed_map_valid
  · exact Pair04_04.every_listed_map_valid
  · exact Pair05_05.every_listed_map_valid
  · exact Template6.every_listed_map_valid
  · exact Pair07_07.every_listed_map_valid
  · exact Pair08_08.every_listed_map_valid
  · exact Pair09_09.every_listed_map_valid
  · exact Pair10_10.every_listed_map_valid
  · exact Pair11_11.every_listed_map_valid
  · exact Pair12_12.every_listed_map_valid
  · exact Pair13_13.every_listed_map_valid
  · exact Pair14_14.every_listed_map_valid
  · exact Pair15_15.every_listed_map_valid
  · exact Pair16_16.every_listed_map_valid
  · exact Pair17_17.every_listed_map_valid
  · exact Pair18_18.every_listed_map_valid
  · exact Pair19_19.every_listed_map_valid
  · exact Pair20_20.every_listed_map_valid
  · exact Pair21_21.every_listed_map_valid
  · exact Pair22_22.every_listed_map_valid
  · exact Pair23_23.every_listed_map_valid
  · exact Pair24_24.every_listed_map_valid
  · exact Pair25_25.every_listed_map_valid
  · exact Pair26_26.every_listed_map_valid
  · exact Pair27_27.every_listed_map_valid
  · exact Pair28_28.every_listed_map_valid
  · exact Pair29_29.every_listed_map_valid
  · exact Pair30_30.every_listed_map_valid
  · exact Pair31_31.every_listed_map_valid
  · exact Pair32_32.every_listed_map_valid
  · exact Pair33_33.every_listed_map_valid
  · exact Pair34_34.every_listed_map_valid
  · exact Pair35_35.every_listed_map_valid
  · exact Pair36_36.every_listed_map_valid
  · exact Pair37_37.every_listed_map_valid
  · exact Pair38_38.every_listed_map_valid
  · exact Pair39_39.every_listed_map_valid
  · exact Pair40_40.every_listed_map_valid
  · exact Pair41_41.every_listed_map_valid
  · exact Pair42_42.every_listed_map_valid
  · exact Pair43_43.every_listed_map_valid
  · exact Pair44_44.every_listed_map_valid
  · exact Pair45_45.every_listed_map_valid
  · exact Pair46_46.every_listed_map_valid
  · exact Pair47_47.every_listed_map_valid
  · exact Pair48_48.every_listed_map_valid
  · exact Pair49_49.every_listed_map_valid
  · exact Pair50_50.every_listed_map_valid
  · exact Pair51_51.every_listed_map_valid
  · exact Pair52_52.every_listed_map_valid
  · exact Pair53_53.every_listed_map_valid
  · exact Pair54_54.every_listed_map_valid
  · exact Pair55_55.every_listed_map_valid
  · exact Pair56_56.every_listed_map_valid
  · exact Pair57_57.every_listed_map_valid
  · exact Pair58_58.every_listed_map_valid
  · exact Pair59_59.every_listed_map_valid
  · exact Pair60_60.every_listed_map_valid
  · exact Pair61_61.every_listed_map_valid
end C13.Enumeration.Canonical
