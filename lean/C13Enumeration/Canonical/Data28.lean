import C13Enumeration.Canonical.Core
import C13Enumeration.DegreeSeven.Source26
import Mathlib.Data.Fin.VecNotation
import C13Enumeration.DegreeEightPilot.Source26Center08
namespace C13.Enumeration.Canonical.Data28
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

abbrev matrix := DegreeEightPilot.Source26Center08.matrixA
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link26 8) a b := DegreeEightPilot.Source26Center08.matrixA_checked

def template : Template where
  family := link26
  center := 8
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source26.avoids_hole
  matrix := matrix
  matrix_checked := matrix_checked
end C13.Enumeration.Canonical.Data28
