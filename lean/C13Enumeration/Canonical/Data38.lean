import C13Enumeration.Canonical.Core
import C13Enumeration.DegreeSeven.Source36
import Mathlib.Data.Fin.VecNotation
import C13Enumeration.Pilot.Source36Center04
namespace C13.Enumeration.Canonical.Data38
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

abbrev matrix := Pilot.Source36Center04.A
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link36 4) a b := Pilot.Source36Center04.A_checked

def template : Template where
  family := link36
  center := 4
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source36.avoids_hole
  matrix := matrix
  matrix_checked := matrix_checked
end C13.Enumeration.Canonical.Data38
