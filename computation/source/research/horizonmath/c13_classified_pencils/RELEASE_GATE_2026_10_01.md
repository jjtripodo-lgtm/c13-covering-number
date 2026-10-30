# C13 global-30 release-gate research log

**Date:** 1 October 2026 (Pacific)  
**Project:** C(13,7,4) covering number  
**Goal:** harden the internally proved exact value `C(13,7,4)=30` into a one-command, fail-closed release gate.

## Why this was the highest-leverage move

Current `main` has already advanced beyond the historical class-12/class-14 profile frontier. The classified-pencil packet excludes every 29-block cover across all 67 Figure-1 completion classes plus the exceptional Figure-6 class, conditional on the published complete classification of minimum (12,6,3) covers. An explicit 30-block cover checks all 715 quadruples.

At that point the main scientific risk is no longer another local residual-profile search. It is assurance drift: a future edit can silently change a proof script, frozen receipt, source transcription, positive control, or report without forcing the entire global proof chain to replay.

This packet therefore adds a deliberately expensive but compact release gate.

## Gate

Run from this directory:

```bash
python release_gate.py
```

The gate fails closed unless all of the following hold.

1. Every file named by `verification_manifest.json` still has its frozen SHA-256.
2. `verify_pencils.py` succeeds in normal Python.
3. The same primary proof succeeds under `python -O`.
4. The two primary outputs are semantically identical and equal the frozen `primary_replay.json`.
5. `independent_raw_replay.py` succeeds in normal Python.
6. The independent replay also succeeds under `python -O`.
7. The two independent outputs are semantically identical and equal the frozen `independent_replay.json`.
8. The headline census is checked explicitly:
   - 68 root classes;
   - 67 Figure-1 classes plus Figure 6;
   - 33,660 labeled choices of four additional minimum points;
   - 31,263 pair-closed cases;
   - 2,355 arc-closed cases;
   - 42 joined residual cases;
   - 280,152 compatible joined tuples;
   - minimum compatible union size 15;
   - zero surviving 14-block outside-pencil assignments;
   - positive 30-cover control covers all 715 quadruples.
9. The primary and independent domain digests both equal
   `425ec3b48e8eecdcc3eb5ac1dbe2555b28420967ea7db00cb690c1e44ddbcb5e`.
10. `test_classified_pencils` passes in both normal and optimized Python.
11. The native-review manifest is fully hash/size checked.
12. The catalog-relative C++ replay compiles with strict warnings, reproduces
    frozen output SHA-256
    `b06bc67b873b1969da5b0219af89fa9a7c955573084af0855333285e43b368ff`,
    and passes its receipt validator.
13. A second C++ build with UBSan and libstdc++ assertions produces
    byte-identical output with no diagnostics.

The result status is:

```text
PASS_C13_GLOBAL30_RELEASE_GATE
```

only after the complete chain above succeeds.

## Scientific boundary

This gate strengthens reproducibility and regression resistance. It does not reprove Gordon, Patashnik, Petro and Taylor's external classification theorem for minimum (12,6,3) covers, establish novelty, substitute for external human review, or formalize the theorem in a proof assistant.

The internally supported theorem remains:

```text
C(13,7,4)=30
```

conditional on the credited published classification and within the packet's stated computational-assurance boundary.

## Hosted verification

The one-command gate passed on GitHub Actions PR #404, run
`36960159390`, job `110691864514`, using Python 3.12.14 and
`g++ 13.3.0`. The tested head was
`2774f418fb75c36556d99326d61f0958fc29a6f2`; the package merged to
`main` at `6118d529d83f2c820b04aaf8f99fb9317c37076a`.

The final receipt reports 14 primary manifest files, 26 native manifest files,
normal/optimized Python equivalence, strict-warning/UBSan native equivalence,
68 root classes, 33,660 minimum-point quadruples, 280,152 compatible tuples,
minimum joined union 15, and the direct 715-quadruple positive control.

Machine-readable receipt:
`artifacts/c13-global30-release-gate-github-2026-10-01.json`.

## Parallel stress test

The historical class-14 split campaign continued as nonessential robustness
work and moved well beyond the earlier 165 -> 156 checkpoint. It is not a
global theorem obligation and should not be treated as publication-critical
progress for `C(13,7,4)=30`.

## Next publication gates

1. Obtain independent external human mathematical review.
2. Broaden the priority search through MathSciNet/zbMATH/citation networks if
   publication is contemplated.
3. Complete final author-accountability and exposition review of the banked
   LaTeX manuscript and referee handoff.
4. Optionally formalize the non-computational reduction and expose the finite
   census through a proof-producing or kernel-checked certificate interface.
5. Keep any public release, submission, or announcement user-directed.
