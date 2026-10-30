# C(13,7,4)=30: hostile assurance audit

**Date:** 1 October 2026 (Pacific)  
**Scope:** private internal theorem audit and release hardening  
**Public action:** not authorized  
**Canonical theorem:** `C(13,7,4)=30`, conditional on the published complete classification of minimum `(12,6,3)` covers.

## Bottom line

I attacked the current exact-30 packet at the reduction, completeness, implementation-independence, and provenance layers.

I did **not** find a mathematical gap in the reduction. The global proof does not depend on the historical class-12/class-14 LP frontiers, Farkas packets, SAT searches, or split sweeps. Its irreducible external mathematical dependency is the Gordon--Patashnik--Petro--Taylor minimum-`(12,6,3)` classification.

The internally decisive chain is:

1. every point of a hypothetical 29-block `(13,7,4)` cover has degree at least 15;
2. the total degree excess over `13*15` is only 8, so at least five points have degree exactly 15;
3. root at one such point, leaving exactly 14 root-avoiding parent blocks;
4. each of four other minimum points has a complete minimum `(12,6,3)` link and therefore a complete outside pencil in an exhaustively reconstructed finite domain;
5. two pencils must agree exactly on their common parent blocks;
6. the union of all four pencils must lie inside the same 14 root-avoiding blocks;
7. the exact global finite census finds no compatible four-pencil tuple with union at most 14;
8. an explicit 30-block cover independently covers all 715 four-subsets.

Therefore no 29-block cover exists and the checked 30-block witness is optimal.

## 1. Reduction audit

### Point-link lower bound

For any point `x`, deleting `x` from the blocks containing it produces a `(12,6,3)` cover: every triple of the other 12 points extends with `x` to a required quadruple. Thus the published equality `C(12,6,3)=15` implies `d(x)>=15`.

No assumption about simplicity or degree regularity is hidden here. Repeated blocks can be deleted without damaging coverage, so an optimal or counterexample cover may be taken simple.

### Five minimum points

For 29 seven-subsets,
```text
sum_x d(x) = 29*7 = 203.
```
The degree-15 baseline is `13*15=195`, leaving exactly eight excess degree units. Every nonminimum point consumes at least one excess unit, so at most eight points can have degree above 15. Hence at least five have degree exactly 15.

This step is tight as an inequality and requires no computational input beyond the published `C(12,6,3)=15`.

### Root budget

Root at one degree-15 point `infinity`. Exactly 15 parent blocks contain it and therefore exactly `29-15=14` avoid it.

Choose four further degree-15 points. No assumption is made about the remaining eight ordinary points.

## 2. Complete-pencil semantics

This is the highest-risk conceptual step, so I re-derived it independently of the code organization.

For a chosen minimum point `q`, its full `q`-link has exactly 15 blocks and is a minimum `(12,6,3)` cover. Inside that link, the blocks containing the root `infinity` are already fixed by the root link. The reconstruction therefore searches every classified minimum source cover and every pointed isomorphism whose **entire** source star at the point corresponding to `infinity` maps to this known star.

After such an isomorphism is fixed, every source block avoiding that source point maps to a root-avoiding parent block containing `q`. There are no optional blocks: the mapped set is the **complete outside pencil through q**.

The primary implementation enumerates unrestricted bijections of the remaining 11 points and verifies whole-star equality. It does not restrict maps to the Figure-1 construction group or a target stabilizer.

The independent raw-source route is materially different. It starts from the literal Figure-1 core and all
```text
28^3 = 21,952
```
raw completions, verifies point transitivity of the raw family, reconstructs its 67 root classes, treats Figure 6 separately at every source center, and uses a different partial-incidence-partition map search. Both routes reconstruct 816 root-class/ordinary-point domains and agree on every domain cardinality and canonical digest.

That closes the most plausible internal common-mode failure: accidentally generating only a subset of possible complete outside pencils.

## 3. Pair consistency and union obstruction

If `P_q` and `P_r` are the complete outside pencils induced by one hypothetical parent cover, then
```text
{B in P_q : r in B} = {B in P_r : q in B}.
```
Both sets are literally the root-avoiding parent blocks containing both `q` and `r`.

Likewise every `P_q` is a subset of the same 14 root-avoiding parent blocks, so
```text
| union_q P_q | <= 14.
```
These are necessary conditions only. The proof does not need to assert that an arbitrary compatible pencil tuple extends to a cover. Showing that **even these necessary conditions are impossible** is enough.

## 4. Finite completeness audit

The global search covers all
```text
68 * C(12,4) = 33,660
```
root-class / labelled four-minimum-point inputs.

The exact partition is
```text
31,263 pair-incompatible
 2,355 arc-consistency closed
    42 exact-join residual
------
33,660 total.
```

The independently authored final join performs no union-budget pruning while generating compatible tuples. Across the 42 residual inputs it enumerates 280,152 pair-compatible four-pencil tuples and measures the literal union only after compatibility has been established. Every union has size 15.

Thus the computational conclusion is stronger than merely “no tuple happened to survive a pruned search”: the unpruned compatible set itself has minimum union 15.

## 5. Upper-bound and padding audit

The explicit 30-block witness has 30 distinct 7-subsets and independently covers all `C(13,4)=715` quadruples.

If a cover with fewer than 29 blocks existed, duplicate blocks could first be removed and then unused 7-subsets added until there were 29 distinct blocks. Adding blocks cannot destroy coverage. Since there are far more than 29 possible 7-subsets, the padding step is legitimate. Therefore excluding 29 excludes all smaller sizes as well.

## 6. Independence and common-mode risk map

| Risk | Current mitigation | Residual status |
| --- | --- | --- |
| Published `C(12,6,3)=15` or classification scope misread | primary-source page audit, source hash, theorem/figure crosscheck | **External theorem dependency remains** |
| Figure-1 completion family incomplete | literal core + all 21,952 raw completions in independent route | Strongly mitigated |
| Figure-6 omitted | separately encoded, source-audited, and exercised by negative control | Strongly mitigated |
| Pointed star maps accidentally restricted | unrestricted whole-star bijections in primary; different partition search in independent route | Strongly mitigated |
| Frozen catalog silently incomplete | independent raw quotient rebuilt and compared against all 68 catalog entries | Strongly mitigated |
| Domain receipt self-confirms producer | raw-source route rebuilds domains by separate algorithm before matching digests | Strongly mitigated |
| Arc consistency deletes valid pencils | only deletes values lacking literal support; residuals sent to exact join | Strongly mitigated |
| Final join prunes away a counterexample | separately authored **unpruned** six-relation join | Strongly mitigated |
| Python assertions disappear under `-O` | promoted checks use explicit exceptions; normal/`-O` receipts agree | Strongly mitigated |
| Language/runtime-specific bug | native C++ rerun with strict warnings and sanitizer path | Strongly mitigated |
| Known 30-cover invalid | separate full-715 coverage checks and minimum-point controls | Strongly mitigated |
| Stale/corrupt historical packet contaminates theorem | exact-30 chain does not import legacy class-profile packets | **Verified separation** |
| Public priority/novelty | bounded search only | **Open; no novelty claim** |
| Human mathematical review | internal reviews only | **Open external gate** |

## 7. Deliberate provenance failure retained

During this hard push, a hosted one-sided class-14 exploratory workflow exposed a malformed historical compressed certificate file used by an older 13-profile split-batch verifier: its base64 payload failed decoding on a fresh checkout.

That failure is useful evidence about why the theorem must have a clean dependency graph. It is **not** a failure of the global exact-30 proof: the classified-pencil proof imports none of those class-14 split packets. The newer independent Wave-1/Wave-2 local replay also avoided that historical batch and reached its own exact 138-profile checkpoint independently.

The malformed artifact should remain quarantined as historical provenance unless separately repaired and re-audited. It must not be cited as theorem support.

## 8. Additional local robustness work from this push

Before the global exact theorem became canonical, this push also hardened the superseded class-14 lane:

- added a clean-room exact split verifier with no imports from the primary C13 split verifier;
- caught and repaired an over-strong checker assumption that two independent profile-0 proofs must use the same branch variable;
- independently replayed Wave 1 and Wave 2 to a 138-profile local frontier;
- ran a symmetry-guided 12-variable split search;
- froze and exactly replayed three further genuinely new local eliminations at residual indices `55,58,73`, giving a local 135-profile frontier.

These results are now regression/provenance evidence only. They are not needed by the global `C(13,7,4)=30` proof and should not distract future agents from theorem assurance and exposition.

## 9. Fresh-checkout release gate

The dedicated hosted gate
`.github/workflows/c13-exact30-clean-checkout.yml` completed successfully on
GitHub Actions run **36959920875** at commit
`36bb91e70f944a4658255695714af6a65adf0556`.

The clean checkout passed, in order:

1. frozen Python and native manifest hash checks;
2. fresh primary and independently structured Python replays;
3. byte identity of normal and optimized-Python receipts;
4. Python positive and corruption controls in both modes;
5. a fresh native C++ build with strict warnings;
6. a second native build with UBSan and libstdc++ assertions;
7. byte identity of optimized and UBSan native receipts;
8. native receipt and minimum-point controls;
9. the final fail-closed gate.

The initial workflow triggered only on edits to its own YAML file. That was a
release-engineering weakness: later proof changes could have bypassed the gate.
Commit `9c8c8385ce930ea8f518fbe1b4d8a7c06f1003e9` first closed that hole with
a broad C13 trigger. Commit
`4140955de536386baa3f17fac71d95c82b339380` then narrowed the trigger to
the manifest-bound proof inputs, primary/independent replay code and receipts,
source audit, theorem report, and native-review tree. This preserves automatic
post-merge theorem replay while avoiding expensive full proof runs for
documentation-only edits.

A successful hosted gate materially improves reproducibility assurance. It
still does not substitute for an external human mathematical referee or
priority review.

## 10. Decision boundary

**Internal mathematical status:** exact theorem packet, with a coherent reduction and multiple exact independent replay layers.

**What remains before a public claim should be considered:** external human mathematical review, broader bibliographic/priority review, final authorship/accountability decisions, and any user-directed release decision.

No repository visibility change, preprint upload, journal submission, outreach, benchmark update, or other public action is authorized by this audit.
