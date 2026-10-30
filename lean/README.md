# Replaying the classification-relative Lean proof

The 1,751 original local modules are copied byte for byte. The package layout and Lake configuration are new; no theorem source was edited. The preserved historical build and axiom records describe their original execution scope. A fresh public-package build has not yet been executed in this release session because its environment lacks Lean and Lake.

Install the official toolchain specified in `lean-toolchain`, then obtain the revision-pinned dependencies with Lake. With those dependencies available, from this directory:

```sh
lake build C13Global.Final C13Global.Statistics
lake env lean --trust=0 -j 1 -M3072 C13Global/AuditFinal.lean > axiom-audit.log
```

Lake builds imported local modules from the included source. Start with no `lean/.lake/build` directory to rebuild local objects. Upstream Mathlib caches, if used, are a separate trust/reproduction boundary: recording their use is necessary, and such a run is not a clean rebuild of upstream sources. To replay every imported proof from source, rebuild upstream dependencies too. Builds are resource intensive; the original work split certificates to respect a 3 GiB per-process cap. Do not infer parallel whole-project memory requirements from that cap.

The public library roots cover seven namespaces: C13, C13Arc, C13Raw, C13Covering, C13Enumeration, C13RawStarRecovery, and C13Global. There are no private path dependencies. Mathlib and its eight dependencies are locked in `lake-manifest.json`. Preserve the lock; do not replace it with a newer Mathlib revision during a reproduction.

Principal mathematical endpoint:

```lean
C13.Global.exact30_after_published_results
```

Its two assumptions are `C13.PublishedMinimumBound C13.Point` and `C13.SourceData.PublishedClassification1995`. The alternative `exact30_after_published_classification` retains the latter predicate. Neither endpoint proves the 1995 classification. The unconditional upper witness is separate. Read `../PROOF_CORRESPONDENCE.md` before describing the result as formalized.

`python3 ../verify_release.py` checks source identity, local import closure, dependency locks, and the preserved historical audit. It cannot substitute for executing the commands above.
