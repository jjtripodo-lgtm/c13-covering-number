C(13,7,4) = 30 -- private referee-preparation package
29 October 2026

Start with C13_manuscript.pdf (eight pages) and AUDIT_REPORT.txt.
The manuscript is an edited copy of the established original four-pencil proof,
not a new claim of discovery. Its mathematical dependency is Gordon, Patashnik,
Petro and Taylor, Minimum (12,6,3) Covers, Ars Combinatoria 40 (1995), 161-177.

REPLAY
Unpack this directory, install Python 3.10 or later, and run:

    python3 reproduce.py

This uses only the Python standard library and requires no network, account,
private repository, solver, or cached bytecode. It executes two structurally
different lower-bound implementations in ordinary and optimized Python, checks
their full outputs against the frozen receipts, and runs corruption, positive,
source-reconstruction and differential controls. Allow several minutes; timing
depends on the machine. Results are written to replay-output/.

For the additional C++ and undefined-behavior-sanitizer cross-check, install a
C++17 compiler and OpenSSL development library, then run:

    python3 reproduce.py --native

For quick integrity and control checks without the full lower-bound census:

    python3 reproduce.py --check-only

A quick-control PASS is not a full-census PASS. MANIFEST.json records SHA-256
digests; SOURCE_GIT_BLOBS.json records original file identities. The manifest
does not authenticate its own origin or substitute for an independently trusted
archive identifier. Frozen historical evidence and fresh audit-results/ are
separate. The original release_gate.py is retained unchanged in the source tree.

WHAT IS INCLUDED
* Edited manuscript PDF and TeX, including a cache-transport justification and
  the literal Figure-1/Figure-6 classification inputs.
* Complete frozen classified-pencil proof directory, including Python source,
  catalog, domain receipts, historical reviews, tests, and native cross-check.
* Fresh ordinary/optimized Python and optimized/UBSan native outputs and controls.
* A new deterministic mixed-hypergraph and literal Cartesian-product audit.
* A bounded prior-art screen, exact trust boundary, and submission checklist.

The historical source directory also contains ancillary optimal-30 rigidity
material. Those auxiliary classifications are not used by this manuscript's
lower-bound chain and were not freshly re-audited here.

RELEASE STATUS
Prepared for independent mathematical review; not cleared for submission.
No public archive DOI exists for this package yet. No public upload, journal
submission, external contact, licensing decision or repository visibility
change has been performed. No new license grant is made by this private packet.
External specialist review, fresh original-figure transcription review,
bibliographic priority clearance, author declarations and archive registration
remain listed in AUDIT_REPORT.txt. The complete Lean package is not included
or freshly rebuilt; the paper's computational proof does not require it.
