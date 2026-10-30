import C13Enumeration.Census.BlockData
namespace C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem blockValid12 : (((blockCodes.drop 384).take 32).all validBlockB) = true := by decide +kernel
theorem blockValid13 : (((blockCodes.drop 416).take 32).all validBlockB) = true := by decide +kernel
theorem blockValid14 : (((blockCodes.drop 448).take 32).all validBlockB) = true := by decide +kernel
end C13.Enumeration.Census
