# C(13,7,4)=30 publication and referee handoff

**Date:** 1 October 2026  
**Status:** private internal handoff; exact theorem packet banked; no public action authorized

## One-sentence result

Conditional on the published exhaustive classification of minimum
`(12,6,3)` covers, the banked exact finite computation excludes every
29-block `(13,7,4)` cover. Together with the independently checked 30-block
construction, this gives `C(13,7,4)=30`.

## What a referee should check first

The proof has one mathematical reduction and one finite completeness claim.

### Reduction

Let `B` be a hypothetical 29-block `(13,7,4)` cover.

- Every point has degree at least 15 because its link is a `(12,6,3)` cover.
- `sum_x d(x)=29*7=203`, while `13*15=195`; therefore only eight excess
  degree units exist and at least five points have degree exactly 15.
- Choose one minimum point `infinity` and four other minimum points.
- The link at `infinity` is a classified 15-block minimum cover. Exactly
  `29-15=14` parent blocks avoid `infinity`.
- For each other minimum point, its 15-block minimum link and the already-known
  root-containing star determine one element of a finite, exhaustively
  reconstructed outside-pencil domain.
- For two selected minimum points, the two outside pencils must agree exactly
  on the blocks containing both points.
- All four pencils live inside the same 14 root-avoiding blocks, so their union
  has size at most 14.

The finite calculation proves that no compatible four-pencil choice has union
size at most 14.

### Finite completeness claim

The production and independent routes cover all 68 root-link types and all
`68 * binom(12,4)=33,660` labelled four-point choices.

| Gate | Count |
| --- | ---: |
| pair-incompatible | 31,263 |
| arc-consistency closed | 2,355 |
| exact-join residual | 42 |
| total | 33,660 |

For the 42 residual cases, the separately authored unpruned join enumerates
280,152 pair-compatible four-pencil tuples. Every one has union size exactly
15. Therefore none fits the 14-block outside budget.

## Why the domain reconstruction is meant to be exhaustive

This is the most important place to attack.

The published classification says every degree-15 link is isomorphic to a
Figure 1 completion or the exceptional Figure 6 cover. The proof does not
restrict star maps to the 576-element Figure-1 construction group or to a
target stabilizer. For a source point of the required degree it enumerates
unrestricted bijections of the remaining 11 points that carry the entire
source star to the known target star, then maps every source block avoiding the
source point. Thus each resulting pencil contains **all** outside blocks
through the target point.

A separately written route starts from the literal Figure-1 core and all
`28^3=21,952` raw completions rather than trusting the 67-representative
catalog as the source of completeness. Figure 6 is handled separately. Both
routes reconstruct 816 root-class/ordinary-point domains and agree on every
domain cardinality and canonical digest.

## Positive controls and failure controls

- The explicit 30-block cover contains 30 distinct 7-sets and covers all
  `binom(13,4)=715` required quadruples.
- Its actual minimum-point pencils survive the domain machinery at the correct
  15-block budget, guarding against accidental use of a 29-specific rule in a
  30-block control.
- A synthetic compatible 14-block tuple survives the generic join algorithm.
- Corrupted catalog, omitted Figure 6, duplicate-block, malformed-ID, bad
  star-map, inconsistent-shared-pencil, and corrupted-30-cover controls are
  included among the focused tests.
- All explicit proof checks remain active under `python -O`.

## Reproduction

From `research/horizonmath/c13_classified_pencils`:

~~~bash
python3 verify_pencils.py > primary.json
python3 -O verify_pencils.py > primary-O.json
python3 independent_raw_replay.py > independent.json
python3 -O independent_raw_replay.py > independent-O.json
cmp primary.json primary-O.json
cmp independent.json independent-O.json
python3 -m unittest test_classified_pencils -v
~~~

The frozen verification manifest is `verification_manifest.json`. It binds
the primary and independent code, replay receipts, catalog, reconstructed-domain
receipt, positive control, source audit, scientific review and theorem report by
SHA-256.

The additional native review is under `native_review/`. Its reviewer compiled
the supplied C++ implementation with strict warnings, reran it, reproduced the
816 domains / 33,660 foursets / 42 joins / 280,152 tuples / zero valid
five-minimum 30-completions, and reran the hardened receipt validator.

## Source dependency

The external mathematical dependency is:

D. M. Gordon, M. Patashnik, S. Petro and J. Taylor,
*Minimum (12,6,3) Covers*, Ars Combinatoria 40 (1995), 161-177.

The source audit pins the inspected author PDF and checks:

- Theorem 4.4: `C(12,6,3)=15`.
- Theorem 5.9: exhaustive Figure-1-completion / Figure-6 classification.
- the Figure 1 and Figure 6 block data used by the reconstruction.

The external classification is credited, not reproved.

A post-promotion dependency lock is banked in
`CLASSIFICATION_DEPENDENCY_AUDIT_2026_10_01.md`. Its executable checker
regenerates all 21,952 literal Figure-1 completions, reconstructs the
576-element quotient action and 67 Figure-1 classes, includes Figure 6
separately, matches all 68 frozen links, and checks both pointed-star mapping
implementations against brute force on 1,536 finite relabeling cases. This
hardens the repository's *use* of Theorem 5.9 without pretending to reprove
the published classification itself.

## Prior-art boundary

The bounded 1 October source audit checked the classification paper, the older
30-block construction literature, later lower-bound work, the public Dwares
C13 repositories, HorizonMath's current benchmark snapshot, and exact-parameter
web/GitHub variants. It found public Dwares work eliminating five project-local
link classes but explicitly leaving the global problem open, and found no prior
global `C(13,7,4)=30` proof.

That is **not** novelty clearance. The live La Jolla table was unavailable
during one direct refresh and indexed copies still showed the historical
28--30 interval. A comprehensive MathSciNet/zbMATH/citation review and external
expert check remain separate gates.

## Referee attack checklist

A useful hostile review should try to break, in order:

1. the degree-count argument forcing five minimum points;
2. the use and exact scope of the published classification;
3. completeness of the raw Figure-1 completion family;
4. inclusion and treatment of Figure 6;
5. unrestrictedness of pointed star maps;
6. the claim that a selected pencil is the **complete** outside pencil through
   its minimum point;
7. the exact pair-consistency equality;
8. the implication `|union P_q| <= 14`;
9. the partition `31,263 + 2,355 + 42 = 33,660`;
10. the 280,152-tuple independent join and its union-size calculation;
11. simple-cover versus repeated-block conventions and the padding argument;
12. independence and correctness of the explicit 30-cover check.

Any failure above should demote the theorem immediately. No solver timeout or
floating-point infeasibility is used in the promoted proof.

## Release blockers

Before a public mathematical claim, the strongest remaining gates are:

- independent external human review;
- a clean replay from a fresh checkout against the frozen manifest;
- broader bibliographic/priority review;
- final LaTeX exposition and authorship/accountability decisions;
- optional formal or proof-producing verification of the finite census.

No email, upload, repository visibility change, benchmark submission, preprint,
or journal submission is authorized by this handoff.
