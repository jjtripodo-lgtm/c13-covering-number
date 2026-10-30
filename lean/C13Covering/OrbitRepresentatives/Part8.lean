import C13Covering.OrbitWordSemantics
namespace C13.OrbitPilot.Representatives.Part8
open C13.OrbitPilot.Word
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem representative64 : catalogRepresentative 64 = indexedCompletion (representativeIndex 64) := by decide +kernel

theorem representative65 : catalogRepresentative 65 = indexedCompletion (representativeIndex 65) := by decide +kernel

theorem representative66 : catalogRepresentative 66 = indexedCompletion (representativeIndex 66) := by decide +kernel

end C13.OrbitPilot.Representatives.Part8
