import C13Enumeration.Canonical.Core
import C13Enumeration.DegreeSeven.Source68
import Mathlib.Data.Fin.VecNotation
namespace C13.Enumeration.Canonical.Data61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

def values : Array Nat := #[4,1,1,2,0,4,2,1,1,2,1,1,0,1,4,1,2,0,4,1,2,1,1,2,1,0,1,1,4,2,0,4,1,1,2,1,1,2,0,2,2,2,4,0,4,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,4,0,10,4,4,4,4,4,4,0,2,1,1,1,0,4,4,1,1,1,2,2,0,1,2,1,1,0,4,1,4,1,2,1,2,0,1,1,2,1,0,4,1,1,4,2,2,1,0,2,1,1,1,0,4,1,2,2,4,1,1,0,1,2,1,1,0,4,2,1,2,1,4,1,0,1,1,2,1,0,4,2,2,1,1,1,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def matrix (a b : Point) : Nat := values.getD (13*a.val+b.val) 0
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link figure6 4) a b := by decide +kernel

def template : Template where
  family := figure6
  center := 4
  center_ne := by decide +kernel
  avoids := DegreeSeven.Source68.avoids_hole
  matrix := matrix
  matrix_checked := matrix_checked
end C13.Enumeration.Canonical.Data61
