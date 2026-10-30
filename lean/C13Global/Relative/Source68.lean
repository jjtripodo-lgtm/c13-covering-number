import C13Global.Relative.Source68Cases
import C13Global.Relative.Source68Coverage00
import C13Global.Relative.Source68Coverage01
import C13Global.Relative.Source68Coverage02
import C13Global.Relative.Source68Coverage03
import C13Global.Relative.Source68Coverage04
import C13Global.Relative.Source68Coverage05
import C13Global.Relative.Source68Coverage06
import C13Global.Relative.Source68Coverage07
import C13Global.Relative.Source68Coverage08
import C13Global.Relative.Source68Coverage09
import C13Global.Relative.Source68Coverage10
import C13Global.Relative.Source68Coverage11
import C13Global.Relative.Source68Coverage12
import C13Global.Relative.Source68Coverage13
import C13Global.Relative.Source68Coverage14
namespace C13.Global.Relative.Source68
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source68
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem coverage_checked : quadPoints.all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by
  have he : quadPoints = ((quadPoints.drop 0).take 33) ++ ((quadPoints.drop 33).take 33) ++ ((quadPoints.drop 66).take 33) ++ ((quadPoints.drop 99).take 33) ++ ((quadPoints.drop 132).take 33) ++ ((quadPoints.drop 165).take 33) ++ ((quadPoints.drop 198).take 33) ++ ((quadPoints.drop 231).take 33) ++ ((quadPoints.drop 264).take 33) ++ ((quadPoints.drop 297).take 33) ++ ((quadPoints.drop 330).take 33) ++ ((quadPoints.drop 363).take 33) ++ ((quadPoints.drop 396).take 33) ++ ((quadPoints.drop 429).take 33) ++ ((quadPoints.drop 462).take 33) := by decide +kernel
  rw [he]
  simp only [List.all_append,Bool.and_eq_true,and_assoc]
  exact ⟨coverage_checked00,coverage_checked01,coverage_checked02,coverage_checked03,coverage_checked04,coverage_checked05,coverage_checked06,coverage_checked07,coverage_checked08,coverage_checked09,coverage_checked10,coverage_checked11,coverage_checked12,coverage_checked13,coverage_checked14⟩

theorem all_foursets (halph : AlphabetComplete figure6 alphabets) (hhard : ∀ Q ∈ hardQuads, ActualObstruction figure6 Q)
    (Q : Finset Point) (hQ : Q ∈ (univ.erase hole).powersetCard 4) :
    ActualObstruction figure6 Q :=
  class_census figure6 emptyCases (empty_actual halph) dualQuads
    (dual_actual halph hhard) coverage_checked Q hQ
end C13.Global.Relative.Source68
