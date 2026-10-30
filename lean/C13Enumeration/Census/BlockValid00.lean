import C13Enumeration.Census.BlockData
namespace C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem blockValid00 : (((blockCodes.drop 0).take 32).all validBlockB) = true := by decide +kernel
theorem blockValid01 : (((blockCodes.drop 32).take 32).all validBlockB) = true := by decide +kernel
theorem blockValid02 : (((blockCodes.drop 64).take 32).all validBlockB) = true := by decide +kernel
end C13.Enumeration.Census
