import C13Enumeration.Canonical.Core
import C13Enumeration.DegreeSeven.Source11
import Mathlib.Data.Fin.VecNotation
import C13Enumeration.DegreeEightPilot.Source11Center02
namespace C13.Enumeration.Canonical.Data19
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

abbrev matrix := DegreeEightPilot.Source11Center02.matrixA
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link11 2) a b := DegreeEightPilot.Source11Center02.matrixA_checked

def template : Template where
  family := link11
  center := 2
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source11.avoids_hole
  matrix := matrix
  matrix_checked := matrix_checked
end C13.Enumeration.Canonical.Data19
