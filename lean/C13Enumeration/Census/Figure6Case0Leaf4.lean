import C13Enumeration.Census.Figure6Case0Data
namespace C13.Enumeration.Census.Figure6Case0
open C13 C13.Checker.RawSupport C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
theorem valid4 : rows4.all (fun r => decide (ValidRow figure6 points [(1819,true)] r)) = true := by decide +kernel
theorem cert4 : certificateB columns rows4 276 14 = true := by decide +kernel
end C13.Enumeration.Census.Figure6Case0
