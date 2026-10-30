import C13Global.DirectDual
import C13Global.FastGroups.Source14Part00
namespace C13.Global
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
example : directLeafCheck FastDual14_000.columns Source14.rootCodes link14
    FastDual14_000.points FastDual14_000.rows FastDual14_000.bound = true := by decide +kernel
example : directLeafCheck FastDual14_001.columns Source14.rootCodes link14
    FastDual14_001.points FastDual14_001.rows FastDual14_001.bound = true := by decide +kernel
end C13.Global
