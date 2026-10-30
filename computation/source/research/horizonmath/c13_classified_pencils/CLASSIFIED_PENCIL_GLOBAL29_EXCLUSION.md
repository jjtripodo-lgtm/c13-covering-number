# A classified-minimum-link obstruction to every29-block (13,7,4) cover

Date:1 October2026. Internal exact finite proof packet, pending final landing and
scientific review. No novelty, publication-ready, external-referee or Lean claim.
Source repository baseline: `cea30b94d1ba4db8f4b82a36994ffaed9c9c4772`.

## Exact statement

Using the published minimum(12,6,3)-cover classification, no(13,7,4) cover has
29 blocks. The included explicit30-block cover passes direct coverage checks
on all715 quadruples. Thus the proposed theorem is

**C(13,7,4)=30.**

This is a global statement covering all67 Figure1 completion classes and the
exceptional Figure6 class. It is not an extrapolation from classes12/14,
not a rounded LP bound, and not a solver timeout. Until the packet's final
review and repository reconciliation are complete, the earlier29–30 headline
must remain the canonical claim. The distinction is intentional.

## 1. Published prerequisites and the five minimum points

The external inputs are Gordon, Patashnik, Petro and Taylor, *Minimum(12,6,3)
Covers*, Ars Combinatoria40(1995),161–177, Theorems4.4 and5.9:
C(12,6,3)=15, and every15-block minimum cover is a Figure1-family completion
or the exceptional Figure6 cover. The source theorem is credited, not reproved. A fresh download of the author PDF
(SHA256 `6da3d15935e5eb8eca9e533c60ffb08db48cb335a94f88c007bd449729f8cf79`)
was rendered: pages3/13 visually match every Figure1/Figure6 source block,
and pages7/15 state the two prerequisites. The page/coordinate audit receipt
is banked separately; it is not an independent reproof of the source theorem.
[Author preprint](https://www.dmgordon.org/papers/c-12-6-3.pdf) and
[publisher record](https://combinatorialpress.com/ars-articles/volume-040-ars-articles/minimum-12-6-3-covers/).

In a29-block(13,7,4) cover every point has degree at least15, because its link
is a(12,6,3) cover. The total degree is29·7=203, so the sum of the13 excesses
above15 is203−13·15=8. At most8 points have positive excess. Hence at least5
points have degree exactly15.

Choose one minimum point as the root infinity. Its15 containing blocks form
one of the classified minimum links L after removing infinity. Exactly14
blocks avoid infinity. At least4 of the12 remaining points also have degree15.
Choose any four of them, Q.

## 2. Every minimum point supplies a complete outside pencil

For q in Q, the entire root-containing part of q's minimum link is known:
it consists of the blocks `{infinity} ∪ (B\{q})`, for B in L containing q.
Call its star at infinity the known q-star. It has d_L(q) blocks.

The full q-link is a classified15-block minimum cover. To obtain every possible
q-link, take every classified source link K and every source point c having
degree d_L(q); map c to infinity; enumerate every bijection of the other11
points that takes the c-star of K to the known q-star. The source blocks
avoiding c map to6-sets of the12 ordinary points other than q. Adding q to each
produces a set P_q of7-blocks, the complete outside pencil through q.

Consequently every hypothetical extension determines a member P_q of the
computed finite domain D_q. This pencil has exactly15−d_L(q) blocks and contains
**all**, not merely some, outside blocks through q.

For distinct q,s in Q, the two pencils must agree on their common blocks:

`{B in P_q : s in B} = {B in P_s : q in B}`.

Every selected pencil is a subset of the same14 outside blocks, so necessarily
`|union(q in Q) P_q| <= 14`.

The finite obstruction proves that no such four pencils exist for any root
link or any Q. That is sufficient for the global contradiction. No assumptions
about degrees of the other8 points, LP feasibility, or their covering rows are
needed after this reduction.

## 3. Complete catalogs, unrestricted star maps, and the independent route

The primary route uses all68 frozen representative links. Figure1 consists of
12 full core blocks and3 disjoint short quartets. Each short quartet has
C(8,2)=28 completions, giving28³=21952 labeled completions. The576-element
core/short-partition group partitions these into67 representatives. This is
an exhaustive partition of the raw completion set; no assumption that every
isomorphism preserves the core is needed for completeness. The exceptional
Figure6 cover is included separately.

Every catalog member is directly checked to have15 distinct6-blocks covering
all220 triples. The exceptional member has degree multiset7^10,10^2, while
Figure1 completions have maximum degree9. No exceptional class is discarded.

Star isomorphisms are **unrestricted11-point bijections**. The primary search
prunes only by necessary vertex and pair-incidence signatures, then checks the
whole star set exactly. It does not restrict star maps to the576-element core
group or to a24-element target stabilizer.

The independently written source route starts with a literal core and all21952
raw completions, bypassing the67-source representative catalog for domain
construction. It explicitly verifies12 core-and-short-partition automorphisms
moving every possible pointed source center to0. Thus it may use source
center0 without losing a rooted Figure1 cover: first move the source center
to0 inside the raw family, then apply the unrestricted star map. It enumerates
maps with a different algorithm, comparing full partial-edge incidence
partitions rather than pair signatures. Figure6 is treated at every source
center. It also independently rebuilds the576-element raw-root quotient and
checks every frozen root representative.

Both routes reconstruct816 domains, one for each root-class/ordinary-point
pair, and agree on every domain's cardinality and canonical SHA256. Only62
rooted-star types occur; isomorphic known stars may reuse a domain after an
explicitly verified full star bijection. Transport is a bijection of whole
pencils, not a heuristic symmetry assumption.

Catalog SHA256:
`019af94696fb4cf543fbc741401141d53126200c3193a21193c6720f81a56510`.
Combined domain digest:
`425ec3b48e8eecdcc3eb5ac1dbe2555b28420967ea7db00cb690c1e44ddbcb5e`.

## 4. The finite obstruction and its independently checked remainder

Both production routes examine **every68·C(12,4)=33660 labeled point quadruple**.
They do not assume that fourset orbit labels form a complete quotient.

-31263 quadruples contain a pair with no common-pencil signature
-2355 further quadruples close under exact arc consistency: a pencil is removed
 only if it has no matching pencil at another chosen minimum point
-42 labeled quadruples survive arc consistency and require an integral join

These counts partition the33660 inputs; no count is subtracted twice.

The primary final search enumerates all pair-compatible pencil choices and
rejects unions larger than14. It uses no forced-union intersection or
nonminimum-point degree pruning in the final production version.

A separately authored peer oracle constructs all six binary compatibility
relations on the four domains and joins them. It applies **no union-budget
pruning**: every compatible tuple is enumerated once, checked literally for
all six pair agreements, and only then has its union measured.

Across the42 labeled residual quadruples it finds280152 compatible tuples:
37 Figure1 cases contribute216 each, and5 Figure6 cases contribute54432 each.
**Every one of these280152 unions has exactly15 blocks.** Thus none can be a
subset of14 outside blocks. The earlier orbit-representative crosscheck had
31 cases and277776 tuples; that is a different, explicitly distinguished
census, not the labeled count.

The Cartesian product of four domains can be much larger than the joined set.
The receipt's `potential_cartesian_size` is not a count of tuples actually
looped through or independently checked. Only `compatible_tuples` is that count.

Combining the three exact stages rules out the four minimum points guaranteed
in Section1. No29-block cover exists. A cover with fewer blocks could be padded
with new distinct7-blocks to size29, so those sizes are excluded too. The
explicit30-cover gives the matching upper bound.

## 5. Positive and malformed-input controls

The included30-cover is checked directly on all715 quadruples by set and
bitmask implementations. Its root has degree15 and its three other minimum
points are0,4,8. Each actual outside pencil appears in its freshly generated
domain, and the three actual pencils remain compatible at the15-block budget.
This guards against accidentally imposing29-specific conditions on the control.

The independent join has a synthetic compatible14-block tuple that must survive;
it is a finite-domain algorithm control, not a claimed29-cover. It also rejects
inconsistent shared pencils and malformed block IDs. Eleven focused tests cover
catalog corruption, omission of Figure6, duplicate blocks, Boolean labels,
point-domain errors, star-map positive/negative cases, exact union budgets,
and corrupted30-cover data. All proof checks use explicit exceptions and remain
active under optimized Python.

## 6. Reproduction and remaining assurance boundaries

All proof replay code is standard-library Python. From this directory:

```
python verify_pencils.py > primary.json
python -O verify_pencils.py > primary-O.json
python independent_raw_replay.py > independent.json
python -O independent_raw_replay.py > independent-O.json
cmp primary.json primary-O.json
cmp independent.json independent-O.json
python -m unittest test_classified_pencils -v
python -O -m unittest test_classified_pencils -v
```

The independent replay uses the peer join and rebuilds the raw source catalog
and every domain. It does not import the primary verifier or any old LP/profile
checker. No50MB scout-domain file, floating-point library, SAT/PB solver,
unknown status, or opaque dual packet is needed for either production replay.

The published classification is an external theorem dependency. No proof
assistant has formalized this new reduction or exhaustive computation here.
Independent internal arithmetic/code review is distinct from an external
mathematical referee, a clean third-party replay, and priority certification.
A bounded web search found the older28–30 table and the explicitly limited
public class52 proof; that search is not novelty clearance. No publication,
visibility change, external message, paid service or hosted Actions run is
part of this packet.

## 7. Relation to earlier work

The earlier global28 proof and class12/class14 profile cuts remain provenance.
The new proof's lower-bound chain does not depend on those LP certificates.
It retains the full68-class scope and replaces degree-only necessary conditions
with exact consistency of overlapping classified minimum links.

The preliminary repaired166-profile work and27 depth-one split candidates are
preserved as exploratory history. They are unnecessary for this global proof.
The malformed historical class12 payloads were neither silently fixed nor
trusted. No failed or incomplete legacy replay is used to promote the theorem.
