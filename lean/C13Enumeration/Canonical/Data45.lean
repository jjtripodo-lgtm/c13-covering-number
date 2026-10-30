import C13Enumeration.Canonical.Core
import C13Enumeration.DegreeSeven.Source42
import Mathlib.Data.Fin.VecNotation
namespace C13.Enumeration.Canonical.Data45
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def values : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,1,1,2,2,1,1,1,1,1,1,0,0,1,3,1,2,2,1,1,1,1,1,1,0,0,1,1,3,2,2,1,1,1,1,1,1,0,0,2,2,2,5,3,2,2,3,1,2,1,0,0,2,2,2,3,5,2,2,1,3,2,1,0,0,1,1,1,2,2,4,2,1,1,4,1,0,0,1,1,1,2,2,2,5,2,2,3,4,0,0,1,1,1,3,1,1,2,4,2,2,2,0,0,1,1,1,1,3,1,2,2,4,2,2,0,0,1,1,1,2,2,4,3,2,2,5,2,0,0,1,1,1,1,1,1,4,2,2,2,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def matrix (a b : Point) : Nat := values.getD (13*a.val+b.val) 0
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link42 0) a b := by decide +kernel

def template : Template where
  family := link42
  center := 0
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source42.avoids_hole
  matrix := matrix
  matrix_checked := matrix_checked
end C13.Enumeration.Canonical.Data45
