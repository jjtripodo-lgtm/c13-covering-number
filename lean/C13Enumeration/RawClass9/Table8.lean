import C13Enumeration.RowTable
import C13Raw.Class9.Data8
import C13Enumeration.Template8.Complete
namespace C13.Enumeration.RawClass9
open C13.Checker.RawSupport C13.Checker.RawSupport.Class9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def table8 : RowTable raw8 where
  chunks := [rows8_0,rows8_1,rows8_2,rows8_3,rows8_4,rows8_5,rows8_6,rows8_7,rows8_8,rows8_9,rows8_10,rows8_11,rows8_12,rows8_13,rows8_14,rows8_15,rows8_16,rows8_17,rows8_18,rows8_19,rows8_20,rows8_21,rows8_22,rows8_23,rows8_24,rows8_25,rows8_26,rows8_27]
  flatten_eq := by rfl

theorem point8_checked : raw8.supported.domain.1 = (8 : Point).val := by rfl
end C13.Enumeration.RawClass9
