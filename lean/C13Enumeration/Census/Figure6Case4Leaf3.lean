import C13Enumeration.Census.Figure6Case4Data
namespace C13.Enumeration.Census.Figure6Case4
open C13 C13.Checker.RawSupport C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
theorem valid3 : rows3.all (fun r => decide (ValidRow figure6 points [(3478,true),(1389,false)] r)) = true := by decide +kernel
theorem cert3 : certificateB columns rows3 211 14 = true := by decide +kernel
end C13.Enumeration.Census.Figure6Case4
