import C13Enumeration.Canonical.Core
import C13Enumeration.DegreeSeven.Source43
import Mathlib.Data.Fin.VecNotation
import C13Enumeration.Pilot.Source43Center04
namespace C13.Enumeration.Canonical.Data46
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

abbrev matrix := Pilot.Source43Center04.A
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link43 4) a b := Pilot.Source43Center04.A_checked

def template : Template where
  family := link43
  center := 4
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source43.avoids_hole
  matrix := matrix
  matrix_checked := matrix_checked
end C13.Enumeration.Canonical.Data46
