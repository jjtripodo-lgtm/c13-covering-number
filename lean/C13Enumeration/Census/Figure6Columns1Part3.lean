import C13Enumeration.Census.Figure6Columns1Data
namespace C13.Enumeration.Census.Figure6Case1
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
theorem columnChunk12 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 384).take 32) ((witnesses.drop 384).take 32) = true := by decide +kernel
theorem columnChunk13 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 416).take 32) ((witnesses.drop 416).take 32) = true := by decide +kernel
theorem columnChunk14 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 448).take 32) ((witnesses.drop 448).take 32) = true := by decide +kernel
theorem columnChunk15 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 480).take 32) ((witnesses.drop 480).take 32) = true := by decide +kernel
end C13.Enumeration.Census.Figure6Case1
