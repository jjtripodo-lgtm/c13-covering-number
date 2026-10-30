import C13Enumeration.Census.Figure6Columns2Data
namespace C13.Enumeration.Census.Figure6Case2
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
theorem columnChunk16 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 512).take 32) ((witnesses.drop 512).take 32) = true := by decide +kernel
theorem columnChunk17 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 544).take 32) ((witnesses.drop 544).take 32) = true := by decide +kernel
theorem columnChunk18 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 576).take 32) ((witnesses.drop 576).take 32) = true := by decide +kernel
theorem columnChunk19 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 608).take 32) ((witnesses.drop 608).take 32) = true := by decide +kernel
end C13.Enumeration.Census.Figure6Case2
