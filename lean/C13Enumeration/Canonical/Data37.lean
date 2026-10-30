import C13Enumeration.Canonical.Core
import C13Enumeration.DegreeSeven.Source33
import Mathlib.Data.Fin.VecNotation
import C13Enumeration.Pilot.Source33Center05
namespace C13.Enumeration.Canonical.Data37
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

abbrev matrix := Pilot.Source33Center05.A
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link33 5) a b := Pilot.Source33Center05.A_checked

def template : Template where
  family := link33
  center := 5
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source33.avoids_hole
  matrix := matrix
  matrix_checked := matrix_checked
end C13.Enumeration.Canonical.Data37
