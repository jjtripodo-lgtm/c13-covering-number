import C13Enumeration.Census.Figure6Case1Data
namespace C13.Enumeration.Census.Figure6Case1
open C13 C13.Checker.RawSupport C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
theorem valid3 : rows3.all (fun r => decide (ValidRow figure6 points [(2283,true),(4048,false)] r)) = true := by decide +kernel
theorem cert3 : certificateB columns rows3 209 14 = true := by decide +kernel
end C13.Enumeration.Census.Figure6Case1
