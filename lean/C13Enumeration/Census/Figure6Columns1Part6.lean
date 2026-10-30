import C13Enumeration.Census.Figure6Columns1Data
namespace C13.Enumeration.Census.Figure6Case1
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
theorem columnChunk24 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 768).take 32) ((witnesses.drop 768).take 32) = true := by decide +kernel
end C13.Enumeration.Census.Figure6Case1
