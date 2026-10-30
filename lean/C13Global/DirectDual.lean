import C13Global.FastDual
namespace C13.Global
open C13.SourceData C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The same exact column score, without allocating a mapped list or adding
zero terms. Its equality to the original checker is proved, not assumed. -/
def directCost : List LinearRow → Code → Int
  | [], _ => 0
  | r :: rs, b => if r.test.check b then r.weight + directCost rs b else directCost rs b

theorem directCost_eq (rows : List LinearRow) (b : Code) : directCost rows b = cost rows b := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    simp only [directCost,cost,List.map_cons,List.sum_cons]
    cases h : r.test.check b <;> simp [h,ih,cost]

def directCertificateB (columns : List Code) (rows : List LinearRow)
    (bound : Int) (budget : Nat) : Bool :=
  decide (0 ≤ bound) && decide ((budget : Int) * bound < score rows) &&
    columns.all (fun b => decide (directCost rows b ≤ bound))

theorem directCertificateB_eq (columns : List Code) (rows : List LinearRow)
    (bound : Int) (budget : Nat) : directCertificateB columns rows bound budget =
      certificateB columns rows bound budget := by
  simp only [directCertificateB,certificateB,directCost_eq]

def directLeafCheck (columns root : List Code) (K : Family Point) (Q : Finset Point)
    (rows : List LinearRow) (bound : Int) : Bool :=
  rows.all (fastValidRowB root K Q) && directCertificateB columns rows bound 14

theorem directLeafCheck_sound (columns root : List Code) (K : Family Point) (Q : Finset Point)
    (rows : List LinearRow) (bound : Int)
    (h : directLeafCheck columns root K Q rows bound = true) :
    fastLeafCheck columns root K Q rows bound = true := by
  simpa only [directLeafCheck,directCertificateB_eq,fastLeafCheck] using h
end C13.Global
