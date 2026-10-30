import C13Enumeration.Canonical.Core
import C13Enumeration.DegreeSeven.Source09
import Mathlib.Data.Fin.VecNotation
import C13Enumeration.Template8.Complete
namespace C13.Enumeration.Canonical.Data01
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

abbrev matrix := Template8.matrix
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link09 8) a b := Template8.matrix_checked

def template : Template where
  family := link09
  center := 8
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source09.avoids_hole
  matrix := matrix
  matrix_checked := matrix_checked
end C13.Enumeration.Canonical.Data01
