# Sharp minimum-point rigidity for optimal (13,7,4) covers

Status: separate additive theorem candidate, exact independent coverage replays
PASS. It is additive to the global proof landed via PR327 at main f68a0161098de43ef065635d21590f98b3791692.

**Claim.** Every 30-block (13,7,4) cover has at most four points of degree 15.
This is sharp: the frozen explicit 30-block control has exactly four.

Assume five such points exist and choose one as root. Its fifteen incident
blocks form a minimum (12,6,3) link, hence one of the 68 published classified
links, including Figure6. The four other chosen minimum points have complete
outside-block pencils among the same reconstructed domains used in the global
29 exclusion. Their pairwise common blocks must agree literally.

Crucially, domain construction, pair rejection and arc consistency contain no
outside-budget predicate. They depend only on full minimum-link stars and
shared-block equality. The separate C++ replay starts afresh with all 68 roots
and all 495 labeled foursets per root (33,660 in total). At budget FIFTEEN,
31,263 cases fail pair compatibility and 2,355 fail synchronous arc consistency.
The remaining 42 have budget15 witnesses. The replay contains no budget14
assertion on these mathematical cases; its synthetic small-budget controls
are only tests of the general search helper.

For each residual it enumerates the exact join of all six pair relations,
without union-budget or degree pruning. All 280,152 compatible tuples have
union size exactly fifteen. A hypothetical cover therefore has no additional
outside blocks: its complete thirty-block set is determined by the root link
and that union. The native checker tests every one of the 715 quadruples
against those actual thirty blocks. Every candidate misses between two and
eight quadruples. Hence no cover has five degree15 points.

An independently structured Python computation instead checks the potentially
uncovered quadruples avoiding the four selected nonroot minimum points. All
42 per-case missing-quadruple histograms agree exactly with the native full
715-quadruple replay. Both share the frozen domain data, whose completeness
has a separate raw21,952-completion reconstruction and published-classification
audit in the global proof packet. The native replay reconstructs all 816
domains itself; every hash matches that independently verified frozen packet.

The known30 positive control is checked directly and through the new coverage
bitset helper, covers all715 quadruples, and has root plus three other minimum
points. Thus the helper demonstrably accepts an actual cover and the bound
four is attained.

Run `check_30_rigidity.cpp` with the generated `catalog_bits.hpp`, then
`validate_rigidity.py` against the frozen proof directory and the independent
Python scout receipt. The fresh budget15 output SHA256 is
cbe121161a06e93d15ad351c09e0d5ae69fe2fbbcd63884f53e421b3346546dc.
The receipt checker passes identically under normal and optimized Python.

Boundary: this is a computational structural theorem conditional on the
published complete minimum-link classification, with no novelty claim or
external human/formal proof review. It is distinct from proving the covering
number equals30. Parent owns canonical integration and the exact-candidate common gate before landing.

Eleven receipt controls pass in normal and optimized Python, including missing/duplicate domains, altered hashes, budget14 summary substitution, fabricated covers, missing cases, wrong coverage histograms, negative/bool class counts and false final claims. Portable Python regeneration rebuilds domains from the banked catalog without the unbanked scratch cache.

## A sharp constrained minimum of31

A literal31-block cover with exactly five degree15 points is banked in
`known31_five_minimum_control.json`. It is obtained by adding one block to the
first residual near-cover. Its degrees are
20,18,17,17,16,17,15,17,15,15,20,15,15.
`verify_minimum_point_controls.py` independently checks all715 quadruples and
all point degrees for both the30- and31-block positive controls. Normal and
optimized receipts agree. Combined with the global C13 lower bound and the
new30 exclusion, the minimum number of blocks under the constraint of having
at least five degree15 points is exactly31.
