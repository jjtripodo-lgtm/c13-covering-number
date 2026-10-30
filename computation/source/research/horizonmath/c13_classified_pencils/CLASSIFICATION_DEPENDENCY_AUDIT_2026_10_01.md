# C(13,7,4)=30: classification-dependency lock

**Date:** 1 October 2026  
**Status:** post-promotion publication-assurance audit  
**Theorem status:** internal exact finite theorem; no public action authorized

## Why this is the live seam

The classified-pencil proof of `C(13,7,4)=30` has one external mathematical
hinge: the published classification of minimum `(12,6,3)` covers by Gordon,
Patashnik, Petro and Taylor.

A referee therefore needs two questions kept separate:

1. **What does the published theorem actually say?**
2. **Once that theorem is granted, does this repository exhaust the finite
   objects it says it exhausts?**

This packet hardens the second question and records an independent check of the
first.

## External theorem scope checked

The public publisher record for *Minimum (12,6,3) Covers* states that the
authors construct a 15-block cover, prove 15 is minimal, and classify the
minimum covers. The paper's Theorem 4.4 states `C(12,6,3)=15`. Theorem 5.9
states that every minimum `(12,6,3)` cover is isomorphic either to a completion
of the Figure-1 element-minimal family or to the Figure-6 element-minimal cover,
but not both.

That is exactly the scope the C13 manuscript needs. The classification remains
an **external theorem dependency** and is credited rather than reproved here.

A subtle but important boundary is the paper's later computational remark that
Figure 1 has 67 nonisomorphic completions. The C13 independent replay does not
need to trust that numerical remark as a completeness axiom.

Sources checked during this audit:

- Gordon, Patashnik, Petro and Taylor, *Minimum (12,6,3) Covers*,
  Ars Combinatoria 40 (1995), 161-177.
- Author PDF: https://dmgordon.org/papers/c-12-6-3.pdf
- Publisher record:
  https://combinatorialpress.com/ars-articles/volume-040-ars-articles/minimum-12-6-3-covers/

The already-banked `primary_source_audit.json` independently pins the inspected
author PDF by SHA-256 and records the theorem/figure pages. This new packet does
not replace that receipt.

## New executable dependency lock

`classification_dependency_lock.py` is deliberately narrower than the full
theorem replay. It reconstructs the exact finite source boundary a referee is
most likely to question.

It independently performs the following checks:

1. rebuild the literal 12-block Figure-1 core and the three short quartets;
2. generate all `28^3 = 21,952` labeled Figure-1 completions;
3. reconstruct the 576-element core/short-partition construction group;
4. partition all 21,952 completions and recover exactly 67 representatives;
5. add the exceptional Figure-6 cover separately;
6. compare the resulting 68 literal 15-block links against
   `minimum_link_catalog.json` class by class;
7. check every rebuilt link has 15 distinct 6-sets and covers all
   `C(12,3)=220` triples; and
8. exhaustively compare **both** pointed-star mapping implementations against
   literal brute-force bijections on every simple graph on four vertices under
   every relabeling, for 1,536 mapper instances.

The star-map check is not intended to prove the 11-point case by testing small
examples. Its role is implementation assurance: the production mapper and the
separately authored mapper are both checked against a transparent exhaustive
oracle across a complete nontrivial finite family. Their code also finishes with
exact whole-star equality checks, so the pruning predicates can only discard
maps if an isomorphism invariant is implemented incorrectly.

## What this closes

The independent route in `independent_raw_replay.py` visibly constructs

- the 21,952 raw Figure-1 completions,
- the 576 construction-group quotient,
- 67 Figure-1 representatives, and
- Figure 6 separately,

before it compares those objects with the frozen catalog. The catalog therefore
acts as a cross-check, not the source of the independent completeness claim.

Likewise, the production `star_maps` routine is not restricted to the
576-element Figure-1 construction group or a target stabilizer. It searches
point bijections of the full known star, using degree and pair-incidence
signatures only as necessary pruning conditions, and finally checks exact
whole-star equality.

The independent `maps_by_partitions` routine uses a different partial-incidence
partition search and is separately checked by the same brute-force audit.

## Reproduction

From `research/horizonmath/c13_classified_pencils`:

```bash
python3 classification_dependency_lock.py
python3 -O classification_dependency_lock.py
python3 -m unittest -v test_classification_dependency_lock.py
python3 -O -m unittest -v test_classification_dependency_lock.py
```

Expected status:

```text
PASS_C13_CLASSIFICATION_DEPENDENCY_LOCK
```

Expected headline invariants:

```text
raw Figure-1 completions:        21,952
construction-group order:          576
Figure-1 quotient classes:           67
exceptional Figure-6 classes:         1
literal catalog classes:             68
star-mapper brute-force cases:    1,536
```

## Claim boundary

This packet strengthens assurance for the existing internally banked theorem
`C(13,7,4)=30`. It does **not** reprove the 1995 classification, certify
worldwide novelty or priority, substitute for an external human referee, or
authorize publication, outreach, repository-visibility changes, or submission.

The strongest remaining publication gates are external human mathematical
review, broader database/citation-network priority work if publication is
pursued, and final authorship/accountability decisions.
