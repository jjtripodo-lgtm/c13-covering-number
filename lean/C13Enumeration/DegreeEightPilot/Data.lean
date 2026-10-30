import Mathlib.Data.Fin.VecNotation
import C13Enumeration.CrossSearch
import C13Enumeration.RowTable
import C13Enumeration.RawClass9.CatalogCodes
namespace C13.Enumeration.DegreeEightPilot
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def values : Array Nat := #[5,3,2,2,0,3,2,2,3,1,1,1,0,3,5,2,2,0,3,2,2,1,3,1,1,0,2,2,4,2,0,2,1,1,1,1,3,1,0,2,2,2,4,0,2,1,1,1,1,1,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,2,2,0,4,1,1,1,1,1,1,0,2,2,1,1,0,1,3,1,1,1,1,1,0,2,2,1,1,0,1,1,3,1,1,1,1,0,3,1,1,1,0,1,1,1,3,1,1,1,0,1,3,1,1,0,1,1,1,1,3,1,1,0,1,1,3,1,0,1,1,1,1,1,3,1,0,1,1,1,3,0,1,1,1,1,1,1,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def matrix (a b : Point) : Nat := values.getD (13*a.val+b.val) 0
theorem matrix_checked : ∀ a b, matrix a b = coDegree (link link01 4) a b := by decide +kernel

def codedDomain : CodedDomain where
  point := 4
  alphabet := [988,1466,1657,2422,2741,3283,3859,3861,3862,3865,3866,3868,3889,3890,3892,3896,3921,3922,3924,3928,3952,3985,3986,3988,3992,4016,4048]
  rows := [[0,1,2,3,4,5,6],[0,1,2,3,4,5,7],[0,1,2,3,4,5,8],[0,1,2,3,4,5,9],[0,1,2,3,4,5,10],[0,1,2,3,4,5,11],[0,1,2,3,4,5,12],[0,1,2,3,4,5,13],[0,1,2,3,4,5,14],[0,1,2,3,4,5,15],[0,1,2,3,4,5,16],[0,1,2,3,4,5,17],[0,1,2,3,4,5,18],[0,1,2,3,4,5,19],[0,1,2,3,4,5,20],[0,1,2,3,4,5,21],[0,1,2,3,4,5,22],[0,1,2,3,4,5,23],[0,1,2,3,4,5,24],[0,1,2,3,4,5,25],[0,1,2,3,4,5,26]]

def table : RowTable codedDomain where
  chunks := [codedDomain.rows]
  flatten_eq := by simp

theorem point_label : codedDomain.supported.domain.1 = (4 : Point).val := rfl
theorem row_count : codedDomain.rows.length = 21 := rfl
end C13.Enumeration.DegreeEightPilot
