import C13Enumeration.Canonical.Core
import C13Enumeration.DegreeSeven.Source15
import Mathlib.Data.Fin.VecNotation
import C13Enumeration.Pilot.Source15Center00
namespace C13.Enumeration.Canonical.Data20
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

abbrev matrix := Pilot.Source15Center00.A
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link15 0) a b := Pilot.Source15Center00.A_checked

def template : Template where
  family := link15
  center := 0
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source15.avoids_hole
  matrix := matrix
  matrix_checked := matrix_checked
end C13.Enumeration.Canonical.Data20
