# C13 global-30 third-party replay brief

**Purpose:** enable a clean reviewer to replay the internal finite proof of
`C(13,7,4)=30` without relying on the historical LP/profile campaign.

## Claim under review

Conditional on Gordon, Patashnik, Petro and Taylor's published complete
classification of minimum `(12,6,3)` covers, the repository computation
excludes every 29-block `(13,7,4)` cover. The included 30-block construction
covers all 715 quadruples.

This brief does not ask the reviewer to accept a novelty claim or to reprove
the published classification.

## Minimal replay

From `research/horizonmath/c13_classified_pencils` with Python 3.12:

```bash
python release_gate.py --receipt /tmp/c13-global30-release-gate.json
```

Expected terminal status:

```text
PASS_C13_GLOBAL30_RELEASE_GATE
```

The release gate is intentionally redundant. It verifies frozen evidence
hashes, reruns both complete finite proof engines in normal and optimized
Python, compares the outputs to their frozen receipts, checks the headline
census, and runs the hostile/positive unit tests in both modes.

## Headline invariants

A successful replay must establish all of the following exactly:

- 68 rooted minimum-link classes;
- 67 Figure-1 completion classes plus the exceptional Figure-6 cover;
- 21,952 raw Figure-1 completions in the independent source reconstruction;
- 576 source-core automorphisms;
- 62 rooted-star types;
- 33,660 labeled choices of four additional minimum points;
- 31,263 pair-closed cases;
- 2,355 arc-consistency closures;
- 42 residual joined cases;
- 280,152 compatible four-pencil tuples in the independent join;
- minimum joined union size 15;
- zero surviving assignments whose four complete pencils fit in 14 outside blocks;
- the 30-block positive control covers all 715 quadruples;
- both proof routes agree on domain digest
  `425ec3b48e8eecdcc3eb5ac1dbe2555b28420967ea7db00cb690c1e44ddbcb5e`.

The partition identity
[
31{,}263+2{,}355+42=33{,}660
]
must hold literally.

## Independence map

The **primary route** reads the frozen 68-class catalog and constructs every
root-class/ordinary-point pencil domain.

The **independent route** rebuilds the 21,952 raw Figure-1 completions directly,
reconstructs the quotient and rooted-star domains with a separately structured
algorithm, treats Figure 6 separately, and uses the separately authored
`peer_union_join.py` for the final four-domain join.

The two implementations share the mathematical problem statement and source
classification, but the independent route does not import the primary verifier
or the historical LP/profile machinery.

## Positive and hostile controls

The reviewer should confirm that the test suite:

- accepts the supplied 30-block cover and checks all 715 quadruples;
- retains a synthetic compatible 14-block join control;
- rejects malformed catalog data, omitted Figure 6, duplicate blocks,
  invalid labels/point domains, broken star maps, inconsistent shared pencils,
  out-of-range block IDs, and corrupted positive-control data.

The release gate runs this suite in both ordinary and optimized Python.

## Native compiled cross-check

The same command also verifies the frozen native-review manifest, reconstructs
the catalog header, compiles `check_pencils.cpp` with C++17 strict warnings,
reruns the complete catalog-relative census, and validates the output. It then
builds the same source with UBSan and libstdc++ assertions and requires
byte-identical output with no sanitizer diagnostics.

Expected native status:

```text
PASS_COMPILED_DOMAIN_AND_GLOBAL_CENSUS_CROSSCHECK
```

Expected native output SHA-256:

```text
b06bc67b873b1969da5b0219af89fa9a7c955573084af0855333285e43b368ff
```

The hosted reference run is GitHub Actions run `36960159390`, job
`110691864514`, merged through PR #404.

## External theorem dependency

The finite computation assumes:

1. `C(12,6,3)=15`;
2. every minimum 15-block `(12,6,3)` cover is isomorphic to a Figure-1
   completion or to the exceptional Figure-6 cover.

These are credited to Gordon, Patashnik, Petro and Taylor, *Minimum (12,6,3)
Covers*, Ars Combinatoria 40 (1995), Theorems 4.4 and 5.9. The repository
contains a source-coordinate audit, but not an independent proof of their
classification theorem.

## What would block acceptance

Any of the following is a blocking failure for the internal theorem package:

- a manifest hash mismatch;
- normal and optimized replay disagreement;
- disagreement between primary and independent census/digest;
- any compatible four-pencil tuple with union at most 14;
- a failed positive 30-cover control;
- a hostile test that no longer rejects its corruption;
- discovery that the published classification has narrower scope than used.

Novelty, priority, exposition quality, and external referee acceptance are
separate questions. A successful replay certifies only the stated mathematical
and computational chain.
