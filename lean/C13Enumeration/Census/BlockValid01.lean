import C13Enumeration.Census.BlockData
namespace C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem blockValid03 : (((blockCodes.drop 96).take 32).all validBlockB) = true := by decide +kernel
theorem blockValid04 : (((blockCodes.drop 128).take 32).all validBlockB) = true := by decide +kernel
theorem blockValid05 : (((blockCodes.drop 160).take 32).all validBlockB) = true := by decide +kernel
end C13.Enumeration.Census
