# Exact theorem correspondence

The written theorem is C(13,7,4)=30 using Gordon, Patashnik, Petro and Taylor (1995), Theorems 4.4 and 5.9. Lean proves the remaining finite-cover argument with those mathematical inputs stated explicitly.

| Paper component | Lean source / endpoint | Boundary |
| --- | --- | --- |
| Uniform covers, links, degree sum, five minimum points and padding | `lean/C13Covering/Reduction.lean` | Actual finite sets, not integer surrogates |
| Literal GPPT completion family and exceptional cover | `lean/C13Covering/SourceFigures.lean` | Defines `PublishedClassification1995`; does not prove it |
| All 21,952 literal completion triples covered by catalog | `lean/C13Covering/OrbitAllSources.lean` | Coverage direction; no reliance on pairwise nonisomorphism |
| Complete raw star and pencil alphabets | `lean/C13RawStarRecovery/StarTranslation.lean` and imports | Unrestricted semantic transport |
| Actual-cover obstruction and all-fourset coverage | `lean/C13Global/CensusCore.lean` | Quantifies over genuine global covers and retains classification hypothesis |
| Covering and incident-row validity | `lean/C13Global/RowValidity.lean`, `DualBridge.lean` | Row constraints justified from actual covers before dual use |
| All catalog roots and final lower bound | `lean/C13Global/Final.lean` | `all_catalog_foursets`, `no_cover29` |
| Exact number | `C13.Global.exact30_after_published_results` | Assumes published minimum bound and classification |
| One-predicate corollary | `C13.Global.exact30_after_published_classification` | All-size-15 classification predicate retained; no source-level independence from GPPT minimum theorem |
| Existence of 30-block cover | `lean/C13/Known30.lean`, `C13Covering/PositiveBridge.lean` | Unconditional, previously known upper-bound construction |

## Two certificate routes

The Python complete-pencil proof partitions 33,660 root/fourset positions as 31,263 pair-closed, 2,355 additional arc-closed, and 42 final joins. The unpruned final joins have 280,152 compatible tuples, all with union size 15.

The Lean actual-cover proof uses 31,762 empty-support exclusions, 1,893 integer-dual exclusions (964 representatives plus 929 checked transports), and five exceptional predecessor cases. Their sum is 33,660. This route uses genuine covering-row constraints and does **not** establish the stronger abstract `AllFourChecksFalse` interface merely by having the same census size.

## What the axiom audit means

The preserved original audit records 76,982 project declarations in 1,750 modules, with only `propext`, `Classical.choice`, `Quot.sound` and no unsafe project declaration. Its decoded log SHA-256 is `135372280b757e13aac432d8b6c3055fd1b44ff37e35ab01df5c4fcfdcbe6901`. This is a source-bound historical execution, not a fresh build of the new public packaging. A theorem parameter is not an axiom: a clean axiom report does not turn the conditional endpoint into an unconditional proof of the imported classification.

The exact source identity of every exported module agrees with the original root receipt. External dependency objects are not included as opaque proof replacements. New sources from the later uncompiled 490-case research program are excluded.
