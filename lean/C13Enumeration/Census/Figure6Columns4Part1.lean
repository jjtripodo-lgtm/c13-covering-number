import C13Enumeration.Census.Figure6Columns4Data
namespace C13.Enumeration.Census.Figure6Case4
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
theorem columnChunk04 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 128).take 32) ((witnesses.drop 128).take 32) = true := by decide +kernel
theorem columnChunk05 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 160).take 32) ((witnesses.drop 160).take 32) = true := by decide +kernel
theorem columnChunk06 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 192).take 32) ((witnesses.drop 192).take 32) = true := by decide +kernel
theorem columnChunk07 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 224).take 32) ((witnesses.drop 224).take 32) = true := by decide +kernel
end C13.Enumeration.Census.Figure6Case4
