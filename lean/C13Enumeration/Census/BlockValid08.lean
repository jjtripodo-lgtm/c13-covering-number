import C13Enumeration.Census.BlockData
namespace C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem blockValid24 : (((blockCodes.drop 768).take 32).all validBlockB) = true := by decide +kernel
end C13.Enumeration.Census
