import C13Enumeration.Census.BlockData
namespace C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem blockValid18 : (((blockCodes.drop 576).take 32).all validBlockB) = true := by decide +kernel
theorem blockValid19 : (((blockCodes.drop 608).take 32).all validBlockB) = true := by decide +kernel
theorem blockValid20 : (((blockCodes.drop 640).take 32).all validBlockB) = true := by decide +kernel
end C13.Enumeration.Census
