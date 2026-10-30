import C13Global.Relative.Source68Witnesses
namespace C13.Global.Relative.Source68
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census C13.Global.Source68
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem coverage_checked09 : ((quadPoints.drop 297).take 33).all (fun qs => emptyCoversB emptyCases qs ||
    decide (qs.toFinset ∈ dualQuads)) = true := by decide +kernel
end C13.Global.Relative.Source68
