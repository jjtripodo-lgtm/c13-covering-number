import C13Enumeration.Canonical.Core
import C13Enumeration.DegreeSeven.Source04
import Mathlib.Data.Fin.VecNotation
import C13Enumeration.Pilot.Source04Center00
namespace C13.Enumeration.Canonical.Data07
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

abbrev matrix := Pilot.Source04Center00.A
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link04 0) a b := Pilot.Source04Center00.A_checked

def template : Template where
  family := link04
  center := 0
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source04.avoids_hole
  matrix := matrix
  matrix_checked := matrix_checked
end C13.Enumeration.Canonical.Data07
