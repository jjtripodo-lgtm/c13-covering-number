# The covering number C(13,7,4) is 30

**John Tripodo · Public proof-source edition · 29 October 2026**

[Manuscript PDF](paper/C13_manuscript.pdf) · [TeX source](paper/C13_manuscript.tex) · [Paper-to-Lean map](PROOF_CORRESPONDENCE.md) · [ORCID](https://orcid.org/0009-0006-9180-4953)

This repository contains a classification-assisted computational proof that 30 seven-element blocks are necessary and sufficient to cover all four-element subsets of a thirteen-point set. The contribution is the exclusion of 29 blocks. The 30-block construction is previously known and credited to the La Jolla Covering Repository's Nurmela–Östergård construction.

The argument uses Gordon, Patashnik, Petro and Taylor's published minimum bound and classification of (12,6,3) covers. It does not claim a new proof of that classification. No external human specialist review is claimed, and the revised manuscript is prepared for Hexagon submission.

## Read the result

Incidence counting forces at least five degree-15 points in a hypothetical 29-block cover. One point supplies a classified link. Four others force complete outside pencils whose overlaps must agree, but every compatible tuple requires 15 outside blocks when only 14 are available.

The Python enumeration covers all 33,660 labelled root/fourset configurations. A separately structured unpruned join examines 280,152 compatible tuples. A distinct Lean proof discharges the actual-cover finite obstruction and derives the exact number **relative to explicit published classification assumptions**.

## Reproduce the checks

```sh
python3 verify_release.py
cd computation
python3 reproduce.py
# Optional independent native and UBSan cross-check:
python3 reproduce.py --native
```

The first command authenticates all 1,751 unchanged Lean source modules, checks local import closure and dependency pins, and verifies the preserved historical axiom log. It is not a Lean compiler invocation. The second runs the exact Python proof and hostile/positive controls without network access or private repositories. Native checking requires a C++17 compiler and OpenSSL development files.

For Lean, see [lean/README.md](lean/README.md). The exact endpoint is `C13.Global.exact30_after_published_results` in [Final.lean](lean/C13Global/Final.lean). Its hypotheses are `PublishedMinimumBound` and `PublishedClassification1995`. The one-predicate corollary retains the classification predicate and its documented source-level caveat.

## Assurance at this release

- All exported local Lean sources match both their original Git blobs and source digests in the historical replay receipt.
- The preserved original audit covers 76,982 project declarations in 1,750 modules. It reports only `propext`, `Classical.choice`, and `Quot.sound`, with no unsafe project declarations.
- Historical cached endpoint replay, original source auditing, current source authentication, and fresh compilation are distinct evidence levels. The new public Lake configuration has **not** been freshly compiled in this release session; the environment has no Lean/Lake executable.
- The published classification remains an external mathematical input. A source hash cannot validate a transcription against a historical figure. Fresh visual comparison with the original figures and independent human review remain outstanding.

[Release validation](verification/RELEASE_VALIDATION.json) · [Prior work and source access](PRIOR_ART.md) · [Reviewer guide](REVIEWER_GUIDE.md) · [Export provenance](PUBLIC_EXPORT.md)

## Rights and attribution

Paper: [CC BY 4.0](LICENSE-PAPER). Authored code and Lean formalization: [MIT](LICENSE). Upstream dependencies retain their own licenses and are not vendored here. Literal combinatorial data are credited to their sources. Dated original audit documents are retained as historical records; their pre-publication administrative statements predate this authorized release.

This work used substantial Anthropic Claude and OpenAI ChatGPT/Codex assistance. No part is represented as checked and understood by a human. Automated verification and independently structured programs do not constitute independent human peer review.
