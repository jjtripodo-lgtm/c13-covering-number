import C13Enumeration.RowTable
import C13Raw.Class9.Data6
import C13Enumeration.Template6.Complete
namespace C13.Enumeration.RawClass9
open C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def table6 : RowTable raw6 where
  chunks := [rows6_0,rows6_1,rows6_2,rows6_3,rows6_4,rows6_5,rows6_6,rows6_7,rows6_8,rows6_9,rows6_10,rows6_11,rows6_12,rows6_13,rows6_14,rows6_15,rows6_16,rows6_17,rows6_18,rows6_19,rows6_20,rows6_21,rows6_22,rows6_23,rows6_24,rows6_25,rows6_26,rows6_27]
  flatten_eq := by rfl

theorem point6_checked : raw6.supported.domain.1 = (6 : Point).val := by rfl
end C13.Enumeration.RawClass9
