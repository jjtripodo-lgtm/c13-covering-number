import C13Global.Data.Source01
import C13Global.Data.Source02
import C13Global.Data.Source03
import C13Global.Data.Source04
import C13Global.Data.Source05
import C13Global.Data.Source06
import C13Global.Data.Source07
import C13Global.Data.Source08
import C13Global.Data.Source09
import C13Global.Data.Source10
import C13Global.Data.Source11
import C13Global.Data.Source12
import C13Global.Data.Source13
import C13Global.Data.Source14
import C13Global.Data.Source15
import C13Global.Data.Source16
import C13Global.Data.Source17
import C13Global.Data.Source18
import C13Global.Data.Source19
import C13Global.Data.Source20
import C13Global.Data.Source21
import C13Global.Data.Source22
import C13Global.Data.Source23
import C13Global.Data.Source24
import C13Global.Data.Source25
import C13Global.Data.Source26
import C13Global.Data.Source27
import C13Global.Data.Source28
import C13Global.Data.Source29
import C13Global.Data.Source30
import C13Global.Data.Source31
import C13Global.Data.Source32
import C13Global.Data.Source33
import C13Global.Data.Source34
import C13Global.Data.Source35
import C13Global.Data.Source36
import C13Global.Data.Source37
import C13Global.Data.Source38
import C13Global.Data.Source39
import C13Global.Data.Source40
import C13Global.Data.Source41
import C13Global.Data.Source42
import C13Global.Data.Source43
import C13Global.Data.Source44
import C13Global.Data.Source45
import C13Global.Data.Source46
import C13Global.Data.Source47
import C13Global.Data.Source48
import C13Global.Data.Source49
import C13Global.Data.Source50
import C13Global.Data.Source51
import C13Global.Data.Source52
import C13Global.Data.Source53
import C13Global.Data.Source54
import C13Global.Data.Source55
import C13Global.Data.Source56
import C13Global.Data.Source57
import C13Global.Data.Source58
import C13Global.Data.Source59
import C13Global.Data.Source60
import C13Global.Data.Source61
import C13Global.Data.Source62
import C13Global.Data.Source63
import C13Global.Data.Source64
import C13Global.Data.Source65
import C13Global.Data.Source66
import C13Global.Data.Source67
import C13Global.Data.Source68
namespace C13.Global
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def emptyCaseCounts : List Nat := [Source01.emptyCases.length,Source02.emptyCases.length,Source03.emptyCases.length,Source04.emptyCases.length,Source05.emptyCases.length,Source06.emptyCases.length,Source07.emptyCases.length,Source08.emptyCases.length,Source09.emptyCases.length,Source10.emptyCases.length,Source11.emptyCases.length,Source12.emptyCases.length,Source13.emptyCases.length,Source14.emptyCases.length,Source15.emptyCases.length,Source16.emptyCases.length,Source17.emptyCases.length,Source18.emptyCases.length,Source19.emptyCases.length,Source20.emptyCases.length,Source21.emptyCases.length,Source22.emptyCases.length,Source23.emptyCases.length,Source24.emptyCases.length,Source25.emptyCases.length,Source26.emptyCases.length,Source27.emptyCases.length,Source28.emptyCases.length,Source29.emptyCases.length,Source30.emptyCases.length,Source31.emptyCases.length,Source32.emptyCases.length,Source33.emptyCases.length,Source34.emptyCases.length,Source35.emptyCases.length,Source36.emptyCases.length,Source37.emptyCases.length,Source38.emptyCases.length,Source39.emptyCases.length,Source40.emptyCases.length,Source41.emptyCases.length,Source42.emptyCases.length,Source43.emptyCases.length,Source44.emptyCases.length,Source45.emptyCases.length,Source46.emptyCases.length,Source47.emptyCases.length,Source48.emptyCases.length,Source49.emptyCases.length,Source50.emptyCases.length,Source51.emptyCases.length,Source52.emptyCases.length,Source53.emptyCases.length,Source54.emptyCases.length,Source55.emptyCases.length,Source56.emptyCases.length,Source57.emptyCases.length,Source58.emptyCases.length,Source59.emptyCases.length,Source60.emptyCases.length,Source61.emptyCases.length,Source62.emptyCases.length,Source63.emptyCases.length,Source64.emptyCases.length,Source65.emptyCases.length,Source66.emptyCases.length,Source67.emptyCases.length,Source68.emptyCases.length]
theorem empty_cases_count : emptyCaseCounts.sum = 3636 := by decide +kernel

def emptyFoursetCounts : List Nat := [(quadPoints.filter (emptyCoversB Source01.emptyCases)).length,(quadPoints.filter (emptyCoversB Source02.emptyCases)).length,(quadPoints.filter (emptyCoversB Source03.emptyCases)).length,(quadPoints.filter (emptyCoversB Source04.emptyCases)).length,(quadPoints.filter (emptyCoversB Source05.emptyCases)).length,(quadPoints.filter (emptyCoversB Source06.emptyCases)).length,(quadPoints.filter (emptyCoversB Source07.emptyCases)).length,(quadPoints.filter (emptyCoversB Source08.emptyCases)).length,(quadPoints.filter (emptyCoversB Source09.emptyCases)).length,(quadPoints.filter (emptyCoversB Source10.emptyCases)).length,(quadPoints.filter (emptyCoversB Source11.emptyCases)).length,(quadPoints.filter (emptyCoversB Source12.emptyCases)).length,(quadPoints.filter (emptyCoversB Source13.emptyCases)).length,(quadPoints.filter (emptyCoversB Source14.emptyCases)).length,(quadPoints.filter (emptyCoversB Source15.emptyCases)).length,(quadPoints.filter (emptyCoversB Source16.emptyCases)).length,(quadPoints.filter (emptyCoversB Source17.emptyCases)).length,(quadPoints.filter (emptyCoversB Source18.emptyCases)).length,(quadPoints.filter (emptyCoversB Source19.emptyCases)).length,(quadPoints.filter (emptyCoversB Source20.emptyCases)).length,(quadPoints.filter (emptyCoversB Source21.emptyCases)).length,(quadPoints.filter (emptyCoversB Source22.emptyCases)).length,(quadPoints.filter (emptyCoversB Source23.emptyCases)).length,(quadPoints.filter (emptyCoversB Source24.emptyCases)).length,(quadPoints.filter (emptyCoversB Source25.emptyCases)).length,(quadPoints.filter (emptyCoversB Source26.emptyCases)).length,(quadPoints.filter (emptyCoversB Source27.emptyCases)).length,(quadPoints.filter (emptyCoversB Source28.emptyCases)).length,(quadPoints.filter (emptyCoversB Source29.emptyCases)).length,(quadPoints.filter (emptyCoversB Source30.emptyCases)).length,(quadPoints.filter (emptyCoversB Source31.emptyCases)).length,(quadPoints.filter (emptyCoversB Source32.emptyCases)).length,(quadPoints.filter (emptyCoversB Source33.emptyCases)).length,(quadPoints.filter (emptyCoversB Source34.emptyCases)).length,(quadPoints.filter (emptyCoversB Source35.emptyCases)).length,(quadPoints.filter (emptyCoversB Source36.emptyCases)).length,(quadPoints.filter (emptyCoversB Source37.emptyCases)).length,(quadPoints.filter (emptyCoversB Source38.emptyCases)).length,(quadPoints.filter (emptyCoversB Source39.emptyCases)).length,(quadPoints.filter (emptyCoversB Source40.emptyCases)).length,(quadPoints.filter (emptyCoversB Source41.emptyCases)).length,(quadPoints.filter (emptyCoversB Source42.emptyCases)).length,(quadPoints.filter (emptyCoversB Source43.emptyCases)).length,(quadPoints.filter (emptyCoversB Source44.emptyCases)).length,(quadPoints.filter (emptyCoversB Source45.emptyCases)).length,(quadPoints.filter (emptyCoversB Source46.emptyCases)).length,(quadPoints.filter (emptyCoversB Source47.emptyCases)).length,(quadPoints.filter (emptyCoversB Source48.emptyCases)).length,(quadPoints.filter (emptyCoversB Source49.emptyCases)).length,(quadPoints.filter (emptyCoversB Source50.emptyCases)).length,(quadPoints.filter (emptyCoversB Source51.emptyCases)).length,(quadPoints.filter (emptyCoversB Source52.emptyCases)).length,(quadPoints.filter (emptyCoversB Source53.emptyCases)).length,(quadPoints.filter (emptyCoversB Source54.emptyCases)).length,(quadPoints.filter (emptyCoversB Source55.emptyCases)).length,(quadPoints.filter (emptyCoversB Source56.emptyCases)).length,(quadPoints.filter (emptyCoversB Source57.emptyCases)).length,(quadPoints.filter (emptyCoversB Source58.emptyCases)).length,(quadPoints.filter (emptyCoversB Source59.emptyCases)).length,(quadPoints.filter (emptyCoversB Source60.emptyCases)).length,(quadPoints.filter (emptyCoversB Source61.emptyCases)).length,(quadPoints.filter (emptyCoversB Source62.emptyCases)).length,(quadPoints.filter (emptyCoversB Source63.emptyCases)).length,(quadPoints.filter (emptyCoversB Source64.emptyCases)).length,(quadPoints.filter (emptyCoversB Source65.emptyCases)).length,(quadPoints.filter (emptyCoversB Source66.emptyCases)).length,(quadPoints.filter (emptyCoversB Source67.emptyCases)).length,(quadPoints.filter (emptyCoversB Source68.emptyCases)).length]
theorem empty_foursets_count : emptyFoursetCounts.sum = 31762 := by
  unfold emptyFoursetCounts
  rw [Source01.empty_count,Source02.empty_count,Source03.empty_count,Source04.empty_count,Source05.empty_count,Source06.empty_count,Source07.empty_count,Source08.empty_count,Source09.empty_count,Source10.empty_count,Source11.empty_count,Source12.empty_count,Source13.empty_count,Source14.empty_count,Source15.empty_count,Source16.empty_count,Source17.empty_count,Source18.empty_count,Source19.empty_count,Source20.empty_count,Source21.empty_count,Source22.empty_count,Source23.empty_count,Source24.empty_count,Source25.empty_count,Source26.empty_count,Source27.empty_count,Source28.empty_count,Source29.empty_count,Source30.empty_count,Source31.empty_count,Source32.empty_count,Source33.empty_count,Source34.empty_count,Source35.empty_count,Source36.empty_count,Source37.empty_count,Source38.empty_count,Source39.empty_count,Source40.empty_count,Source41.empty_count,Source42.empty_count,Source43.empty_count,Source44.empty_count,Source45.empty_count,Source46.empty_count,Source47.empty_count,Source48.empty_count,Source49.empty_count,Source50.empty_count,Source51.empty_count,Source52.empty_count,Source53.empty_count,Source54.empty_count,Source55.empty_count,Source56.empty_count,Source57.empty_count,Source58.empty_count,Source59.empty_count,Source60.empty_count,Source61.empty_count,Source62.empty_count,Source63.empty_count,Source64.empty_count,Source65.empty_count,Source66.empty_count,Source67.empty_count,Source68.empty_count]
  decide +kernel

def dualQueryCounts : List Nat := [Source01.dualQueries.length,Source02.dualQueries.length,Source03.dualQueries.length,Source04.dualQueries.length,Source05.dualQueries.length,Source06.dualQueries.length,Source07.dualQueries.length,Source08.dualQueries.length,Source09.dualQueries.length,Source10.dualQueries.length,Source11.dualQueries.length,Source12.dualQueries.length,Source13.dualQueries.length,Source14.dualQueries.length,Source15.dualQueries.length,Source16.dualQueries.length,Source17.dualQueries.length,Source18.dualQueries.length,Source19.dualQueries.length,Source20.dualQueries.length,Source21.dualQueries.length,Source22.dualQueries.length,Source23.dualQueries.length,Source24.dualQueries.length,Source25.dualQueries.length,Source26.dualQueries.length,Source27.dualQueries.length,Source28.dualQueries.length,Source29.dualQueries.length,Source30.dualQueries.length,Source31.dualQueries.length,Source32.dualQueries.length,Source33.dualQueries.length,Source34.dualQueries.length,Source35.dualQueries.length,Source36.dualQueries.length,Source37.dualQueries.length,Source38.dualQueries.length,Source39.dualQueries.length,Source40.dualQueries.length,Source41.dualQueries.length,Source42.dualQueries.length,Source43.dualQueries.length,Source44.dualQueries.length,Source45.dualQueries.length,Source46.dualQueries.length,Source47.dualQueries.length,Source48.dualQueries.length,Source49.dualQueries.length,Source50.dualQueries.length,Source51.dualQueries.length,Source52.dualQueries.length,Source53.dualQueries.length,Source54.dualQueries.length,Source55.dualQueries.length,Source56.dualQueries.length,Source57.dualQueries.length,Source58.dualQueries.length,Source59.dualQueries.length,Source60.dualQueries.length,Source61.dualQueries.length,Source62.dualQueries.length,Source63.dualQueries.length,Source64.dualQueries.length,Source65.dualQueries.length,Source66.dualQueries.length,Source67.dualQueries.length,Source68.dualQueries.length]
theorem dual_queries_count : dualQueryCounts.sum = 1893 := by decide +kernel
theorem global_scope_arithmetic : 31762 + 1893 + 5 = 33660 := by decide +kernel
end C13.Global
