import C13Enumeration.Census.Figure6Columns1Data
namespace C13.Enumeration.Census.Figure6Case1
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
theorem columnChunk00 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 0).take 32) ((witnesses.drop 0).take 32) = true := by decide +kernel
theorem columnChunk01 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 32).take 32) ((witnesses.drop 32).take 32) = true := by decide +kernel
theorem columnChunk02 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 64).take 32) ((witnesses.drop 64).take 32) = true := by decide +kernel
theorem columnChunk03 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 96).take 32) ((witnesses.drop 96).take 32) = true := by decide +kernel
end C13.Enumeration.Census.Figure6Case1
