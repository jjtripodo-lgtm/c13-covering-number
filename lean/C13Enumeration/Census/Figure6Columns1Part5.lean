import C13Enumeration.Census.Figure6Columns1Data
namespace C13.Enumeration.Census.Figure6Case1
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
theorem columnChunk20 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 640).take 32) ((witnesses.drop 640).take 32) = true := by decide +kernel
theorem columnChunk21 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 672).take 32) ((witnesses.drop 672).take 32) = true := by decide +kernel
theorem columnChunk22 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 704).take 32) ((witnesses.drop 704).take 32) = true := by decide +kernel
theorem columnChunk23 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 736).take 32) ((witnesses.drop 736).take 32) = true := by decide +kernel
end C13.Enumeration.Census.Figure6Case1
