import C13Global.Physical
import C13Enumeration.Canonical.Complete
namespace C13.Global
open Finset C13.SourceData C13.Enumeration C13.Enumeration.Census
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- The bound is taken from a verified normalizer and a complete semantic domain,
including all source centres and every ambient permutation. -/
theorem record_alphabet_complete
    (r : C13.Enumeration.Canonical.Record C13.Enumeration.Canonical.templates)
    (mask : Mask)
    (checked : (C13.Enumeration.relabelDomain
      (C13.Enumeration.Canonical.domains r.template) r.normalizer.symm r.center).alphabet.all
        (fun b => mask.testBit b.toNat) = true)
    (P : Family Point) (hp : P ∈ completeDomain catalog hole r.family hole r.center)
    (B : Finset Point) (hB : B ∈ P) : mask.testBit (encodeTyped B).toNat = true := by
  have hrep := (C13.Enumeration.complete_relabelled_domain catalog hole r.family
    (C13.Enumeration.Canonical.templates r.template).family r.center
    (C13.Enumeration.Canonical.templates r.template).center r.center_ne r.avoids
    (C13.Enumeration.Canonical.domains r.template) r.normalizer r.hole_fixed
    r.center_image r.star_image (C13.Enumeration.Canonical.canonical_complete r.template)).2 P hp
  have hm := represented_block_in_alphabet _ P hrep B hB
  exact List.all_eq_true.mp checked _ hm

end C13.Global
