import C13Enumeration.Census.BlockData
namespace C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem blockValid06 : (((blockCodes.drop 192).take 32).all validBlockB) = true := by decide +kernel
theorem blockValid07 : (((blockCodes.drop 224).take 32).all validBlockB) = true := by decide +kernel
theorem blockValid08 : (((blockCodes.drop 256).take 32).all validBlockB) = true := by decide +kernel
end C13.Enumeration.Census
