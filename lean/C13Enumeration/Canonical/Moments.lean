import C13Enumeration.Canonical.Core
namespace C13.Enumeration.Canonical
set_option Elab.async false
/-- Exact integer invariants of the full incidence profile. No injectivity or
hash assumption is used: equality under transport follows from profile equality. -/
def rowNumber (p : Nat × Multiset (Nat × Nat)) : Nat :=
  p.1 + 14 * (p.2.map fun q => 14 ^ (14*q.1+q.2)).sum

def profileMoments (p : Multiset (Nat × Multiset (Nat × Nat))) : Nat × Nat × Nat :=
  let xs := p.map rowNumber
  (xs.sum,(xs.map fun x => x^2).sum,(xs.map fun x => x^3).sum)

def matrixMoments (A : Point → Point → Nat) : Nat × Nat × Nat :=
  profileMoments (matrixProfile A)
end C13.Enumeration.Canonical
