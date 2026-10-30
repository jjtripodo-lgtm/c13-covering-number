import C13Enumeration.Census.BlockUniverse
import C13Arc.Certificate

namespace C13.Enumeration.Census
open Finset C13.Checker.RawSupport C13.SourceData
set_option Elab.async false

def columnWitnessB (columns : List Code) (alphabet : Point → List Code)
    (Q : Finset Point) (b : Code) : Option Point → Bool
  | none => columns.contains b
  | some q => decide (q ∈ Q) && b.getLsbD q.val && !(alphabet q).contains b

def columnsCertificateB (columns : List Code) (alphabet : Point → List Code)
    (Q : Finset Point) (witnesses : List (Option Point)) : Bool :=
  C13.Checker.Arc.zipAllExact (columnWitnessB columns alphabet Q) blockCodes witnesses

theorem columns_certificate_sound (columns : List Code) (alphabet : Point → List Code)
    (Q : Finset Point) (witnesses : List (Option Point))
    (checked : columnsCertificateB columns alphabet Q witnesses = true)
    (b : Code) (hb : b ∈ blockCodes)
    (supported : ∀ q ∈ Q, b.getLsbD q.val = true → b ∈ alphabet q) :
    b ∈ columns := by
  obtain ⟨w,_,hw⟩ := C13.Checker.Arc.zipAllExact_covers
    (columnWitnessB columns alphabet Q) blockCodes witnesses checked b hb
  cases w with
  | none => simpa only [columnWitnessB,List.contains_iff] using hw
  | some q =>
    have hh : q ∈ Q ∧ b.getLsbD q.val = true ∧ b ∉ alphabet q := by
      simpa [columnWitnessB,Bool.and_eq_true,and_assoc] using hw
    exact (hh.2.2 (supported q hh.1 hh.2.1)).elim

theorem zipAllExact_append_true {A B : Type} {f : A → B → Bool}
    {as cs : List A} {bs ds : List B}
    (ha : C13.Checker.Arc.zipAllExact f as bs = true)
    (hc : C13.Checker.Arc.zipAllExact f cs ds = true) :
    C13.Checker.Arc.zipAllExact f (as ++ cs) (bs ++ ds) = true := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => exact hc
    | cons b bs => simp [C13.Checker.Arc.zipAllExact] at ha
  | cons a as ih =>
    cases bs with
    | nil => simp [C13.Checker.Arc.zipAllExact] at ha
    | cons b bs =>
      have hh : f a b = true ∧ C13.Checker.Arc.zipAllExact f as bs = true := by
        simpa [C13.Checker.Arc.zipAllExact] using ha
      simpa [C13.Checker.Arc.zipAllExact,hh.1] using ih hh.2

end C13.Enumeration.Census
