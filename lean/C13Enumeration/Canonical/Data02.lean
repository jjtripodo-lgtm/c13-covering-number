import C13Enumeration.Canonical.Core
import C13Enumeration.DegreeSeven.Source01
import Mathlib.Data.Fin.VecNotation
import C13Enumeration.DegreeEightPilot.Data
namespace C13.Enumeration.Canonical.Data02
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

abbrev matrix := DegreeEightPilot.matrix
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link01 4) a b := DegreeEightPilot.matrix_checked

def template : Template where
  family := link01
  center := 4
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source01.avoids_hole
  matrix := matrix
  matrix_checked := matrix_checked
end C13.Enumeration.Canonical.Data02
