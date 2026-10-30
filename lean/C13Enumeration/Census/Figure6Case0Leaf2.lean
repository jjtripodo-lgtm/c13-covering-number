import C13Enumeration.Census.Figure6Case0Data
namespace C13.Enumeration.Census.Figure6Case0
open C13 C13.Checker.RawSupport C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
theorem valid2 : rows2.all (fun r => decide (ValidRow figure6 points [(926,false),(1819,false)] r)) = true := by decide +kernel
theorem cert2 : certificateB columns rows2 52 14 = true := by decide +kernel
end C13.Enumeration.Census.Figure6Case0
