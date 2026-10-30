import C13Enumeration.Canonical.Core
import C13Enumeration.DegreeSeven.Source09
import Mathlib.Data.Fin.VecNotation
import C13Enumeration.Template6.Complete
namespace C13.Enumeration.Canonical.Data06
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

abbrev matrix := Template6.matrix
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link09 6) a b := Template6.matrix_checked

def template : Template where
  family := link09
  center := 6
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source09.avoids_hole
  matrix := matrix
  matrix_checked := matrix_checked
end C13.Enumeration.Canonical.Data06
