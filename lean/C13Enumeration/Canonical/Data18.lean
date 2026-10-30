import C13Enumeration.Canonical.Core
import C13Enumeration.DegreeSeven.Source10
import Mathlib.Data.Fin.VecNotation
import C13Enumeration.DegreeEightPilot.Source10Center02
namespace C13.Enumeration.Canonical.Data18
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

abbrev matrix := DegreeEightPilot.Source10Center02.matrixA
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link10 2) a b := DegreeEightPilot.Source10Center02.matrixA_checked

def template : Template where
  family := link10
  center := 2
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source10.avoids_hole
  matrix := matrix
  matrix_checked := matrix_checked
end C13.Enumeration.Canonical.Data18
