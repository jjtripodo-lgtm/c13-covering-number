# Remaining published mathematical premises

The precise predicates are `PublishedMinimumBound C13.Point` in `C13Covering/Reduction.lean` and `PublishedClassification1995` in `C13Covering/SourceFigures.lean`. They are theorem parameters, never Lean axioms.

1. The minimum-bound predicate quantifies over every twelve-element subset U of Fin 13 and every family L of six-subsets covering all triples of U. Its conclusion is 15 ≤ |L|. This is the lower-bound part of Gordon–Patashnik–Petro–Taylor (1995), Theorem 4.4; the upper-bound part is not needed here.
2. The classification predicate says every 15-block (12,6,3) cover is a relabelling of one of the literal Figure-1 completions or Figure 6, with the omitted point tracked. This is the needed direction of their Theorem 5.9. The existing 21,952-source-to-68-catalog orbit theorem is internal and does not replace this geometric classification premise.

A short independent counting proof was assessed, not found. The elementary iterated incidence bound gives only 14. The published improvement excludes a 14-cover by using the structural classification of minimum (11,5,2) covers (Theorem 3.1 and several properties from Section 3), then the pair-degree contradiction in Lemma 4.3. Formalizing those structural inputs is appreciably more than a short arithmetic lemma. The published (12,6,3) classification depends on the longer Section 5 case analysis. Neither premise can responsibly be marked discharged during this census-validation campaign.

Primary source: Gordon, Patashnik, Petro and Taylor, “Minimum (12,6,3) Covers”, Ars Combinatoria 40 (1995), 161–177. Publisher record: https://combinatorialpress.com/ars-articles/volume-040-ars-articles/minimum-12-6-3-covers/ . Indexed publisher PDF: https://combinatorialpress.com/article/ars/Volume%20040/volume-40-paper-12.pdf . The publisher search index supplied the relevant theorem/proof text on 2026-10-10; the direct PDF endpoint returned 404 during this check. No new transcription or full-paper review is claimed here.

## Additional logical reduction found during this campaign

A different route can remove the minimum-bound parameter **relative to the retained classification parameter**. The exact formal classification predicate covers every size-15 cover, not only covers already known to be cardinality-minimal. An independent producer check found an explicit private triple in each of the 1,020 blocks of the 68 catalog families. The Lean certificates and transport proof compiled: every classified 15-cover is block-irredundant. Padding a hypothetical smaller cover to 15 blocks would then contradict irredundancy. The compiled module `CatalogIrredundance` implements this argument. Its compile/audit receipt, not this proposal, determines whether it can be used. This route does not independently establish the published classification theorem.

### Exact strength and non-circularity boundary

`ClassifiesMinimumLinks` is literally `∀ q L, IsCoverOn (univ.erase q) L 6 3 → L.card = 15 → ...`. There is no minimum-cardinality or irredundancy antecedent. Thus the padding inference is non-circular **inside the stated formal interface**. Padding is by distinct elements of the finite set `U.powersetCard 6`; private-triple preservation is proved under arbitrary permutations.

The paper, however, phrases Theorem 5.9 as a classification of minimum covers after establishing the minimum in Theorem 4.4. Consequently, reducing two Lean parameters to one does not by itself remove Theorem 4.4 from the literature justification of the chosen all-size-15 classification predicate. Do not advertise this as an independent proof of that published lower bound, or as proof that the published classification can be invoked with weaker source assumptions. A source-level independence claim would require reviewing and formalizing the relevant classification proof.

