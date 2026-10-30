import C13Enumeration.Certificate
import C13Covering.SourceLiterals
namespace C13.Enumeration.Pilot
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def expected : Family Point :=
 {{0,1,2,4,7,9,10},{0,1,2,5,6,8,11},{0,1,3,4,6,9,11},
  {0,1,3,5,7,8,10},{0,2,3,4,5,10,11},{0,2,3,6,7,8,9}}

def values : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,1,1,3,3,2,2,2,2,2,2,0,0,1,3,1,2,2,1,1,1,1,1,1,0,0,1,1,3,2,2,1,1,1,1,1,1,0,0,3,2,2,5,3,2,2,3,1,1,1,0,0,3,2,2,3,5,2,2,1,3,1,1,0,0,2,1,1,2,2,4,2,1,1,3,1,0,0,2,1,1,2,2,2,4,1,1,1,3,0,0,2,1,1,3,1,1,1,4,2,2,2,0,0,2,1,1,1,3,1,1,2,4,2,2,0,0,2,1,1,1,1,3,1,2,2,4,2,0,0,2,1,1,1,1,1,3,2,2,2,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def matrix (a b : Point) : Nat := values.getD (13*a.val+b.val) 0

theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link01 0) a b := by decide +kernel
end C13.Enumeration.Pilot
