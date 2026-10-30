import C13Global.MaskKernel
import C13Enumeration.Census.DualCertificate
import C13Covering.SourceLiterals

namespace C13.Global
open Finset C13.SourceData C13.Checker.RawSupport C13.Enumeration C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def RawValidRow (K : C13.Family C13.Point) (Q : Finset C13.Point) (r : LinearRow) : Prop :=
  match r.test with
  | .covers t => 0 ≤ r.weight ∧ r.demand = 1 ∧
      decodeTyped t ⊆ univ.erase hole ∧ (decodeTyped t).card = 4 ∧
      ∀ B ∈ K, ¬ decodeTyped t ⊆ B
  | .incident q => q ∈ Q ∧ r.demand = (15 - C13.degree K q : Nat)
  | .block _ => False

instance (K : C13.Family C13.Point) (Q : Finset C13.Point) (r : LinearRow) :
    Decidable (RawValidRow K Q r) := by
  unfold RawValidRow
  split
  · rename_i t ht
    letI : Decidable (∀ B ∈ K, ¬ decodeTyped t ⊆ B) := Finset.decidableDforallFinset
    infer_instance
  · infer_instance
  · infer_instance

def rawLeafCheck (columns : List Code) (K : C13.Family C13.Point) (Q : Finset C13.Point)
    (rows : List LinearRow) (bound : Int) : Bool :=
  rows.all (fun r => decide (RawValidRow K Q r)) && certificateB columns rows bound 14

end C13.Global
