# Independent Erdős700-worker review of classified-pencil exclusion

Reviewed 1 October 2026, completed at approximately05:47 UTC.
This is internal mathematical/computational review, not external human review,
Lean verification, or priority certification.

## Scope and conclusion

No blocking defect found in the mathematical reduction or the reviewed exact
computations. The proof's published minimum-(12,6,3)-cover classification remains
an external theorem dependency; the review does not reprove it.

The reviewer checked:

1. A29-block cover has a degree15 root because each point link needs at least15
   blocks and total degree is203. The twelve nonroot excesses are nonnegative
   and sum8, hence at leastfour other points have degree15
2. At any such point, its complete minimum link is classified; fixing its star
   at the original root and taking every star isomorphism produces the entire
   outside-pencil domain, including non-quartet-preserving maps
3. The independent raw21952 enumeration is complete: twelve explicitly checked
   core/short-block automorphisms move every source center to0. Partial-edge
   incidence-partition pruning is necessary at each prefix and complete once
   all11 points are mapped
4. Transport from a representative rooted-star type to an isomorphic target is
   complete because the representative domain already includes every source
   star isomorphism. The extended map sends the old center to the new center
5. Equality of literal shared-block signatures is necessary for two complete
   pencils. Pair rejection and monotone synchronous arc consistency are sound
6. The independently authored `peer_union_join.py` enumerates every compatible
   four-pencil tuple by joining allsix pair relations. It uses no forced-union,
   degree-capacity, or union-budget pruning; the union size is measured afterward
7. The thirty-block positive control is validated on all715 four-subsets

The literal exceptional link has15 distinct blocks, covers every triple and has
degree10 vertices. Every Figure1 completion has point degree at most9.
Conditional on the classification's unique exceptional type, this provides an
additional identification check, beyond the producer's original-PDF figure audit.

## Replays and independence boundaries

- Independently authored fresh set-based replay of the earlier218 integer cuts:
  all172,656 cut-column pairs and allstrict seed contradictions pass
- Reran the independent raw-domain/495-quadruple implementation for classes12,14
  under Python -O; bothclose all495 zero4-subsets
- The reviewer's independent exact-join implementation checked the31 advertised
  residual orbit representatives:277,776 compatible tuples, allunion15
- After integration into the independent all68/raw-source implementation, the
  reviewer freshly reran the complete final source under Python -O. This is a
  separate execution of the covering worker's independently structured domain
  reconstruction, plus the reviewer's independently authored tuple-join code

Full final-source result:

-68 root classes,21,952 raw completions,576 source-core automorphisms
-62 rooted-star types
-33,660 labeled four-minimum pointsets
-31,263 pair-closed;2,355 arc-closed;42 residual joined cases
-280,152 compatible tuples;minimum joined union15
-715 foursets passed by the30-block positive control

Domain digest:
`425ec3b48e8eecdcc3eb5ac1dbe2555b28420967ea7db00cb690c1e44ddbcb5e`

Reviewer's final replay receipt SHA256:
`870eb68cfc6d79aa995df85ee39d3fb675b4d67c3054c711dd807fad198568f6`

That receipt was byte-identical to the producer's latest full-independent -O
receipt. An older normal-mode receipt lacked only newly added domain-digest
metadata; the producer was instructed to rerun exact final source before
claiming final normal/-O byte equality.

## Hostile controls

The portable join retains a synthetic compatible tuple of exactly14 blocks,
rejects inconsistent shared pencils, and rejects an out-of-range block index.
Thus it is not an always-reject engine. Its huge potential Cartesian cardinality
is explicitly labeled as an input statistic; only actually enumerated compatible
tuples are claimed as checks. The general proof/control suite also includes a
published30-cover whose actual minimum pencils survive domain construction.

No solver status, floating-point inequality, empirical timeout, or assumed
absence of a witness is used as the final contradiction.
