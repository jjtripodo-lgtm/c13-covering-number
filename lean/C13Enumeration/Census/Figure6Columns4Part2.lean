import C13Enumeration.Census.Figure6Columns4Data
namespace C13.Enumeration.Census.Figure6Case4
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
theorem columnChunk08 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 256).take 32) ((witnesses.drop 256).take 32) = true := by decide +kernel
theorem columnChunk09 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 288).take 32) ((witnesses.drop 288).take 32) = true := by decide +kernel
theorem columnChunk10 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 320).take 32) ((witnesses.drop 320).take 32) = true := by decide +kernel
theorem columnChunk11 : C13.Checker.Arc.zipAllExact (columnWitnessB columns Figure6Alphabets.alphabet points) ((blockCodes.drop 352).take 32) ((witnesses.drop 352).take 32) = true := by decide +kernel
end C13.Enumeration.Census.Figure6Case4
