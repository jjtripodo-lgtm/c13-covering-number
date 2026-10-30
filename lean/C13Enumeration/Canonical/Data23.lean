import C13Enumeration.Canonical.Core
import C13Enumeration.DegreeSeven.Source18
import Mathlib.Data.Fin.VecNotation
import C13Enumeration.Pilot.Source18Center00
namespace C13.Enumeration.Canonical.Data23
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

abbrev matrix := Pilot.Source18Center00.A
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link18 0) a b := Pilot.Source18Center00.A_checked

def template : Template where
  family := link18
  center := 0
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source18.avoids_hole
  matrix := matrix
  matrix_checked := matrix_checked
end C13.Enumeration.Canonical.Data23
