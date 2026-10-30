import C13Enumeration.Census.BlockData
namespace C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem blockValid21 : (((blockCodes.drop 672).take 32).all validBlockB) = true := by decide +kernel
theorem blockValid22 : (((blockCodes.drop 704).take 32).all validBlockB) = true := by decide +kernel
theorem blockValid23 : (((blockCodes.drop 736).take 32).all validBlockB) = true := by decide +kernel
end C13.Enumeration.Census
