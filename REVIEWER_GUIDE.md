# A focused referee route

1. Read the five-minimum-point count, domain-completeness lemma, full-star transport argument, and compatible-union contradiction in the manuscript.
2. Check the external GPPT Theorems 4.4 and 5.9 and compare the literal Figure1/Figure6 inputs against the original figures. Source fidelity is separate from finite enumeration.
3. Run `python3 computation/reproduce.py`, then inspect the two domain generators and the independently structured unpruned join. Check all 816 domain identities, all 33,660 positions, and the 280,152 tuple total.
4. Read `PROOF_CORRESPONDENCE.md`, the actual definition of `ActualObstruction`, and `lean/C13Global/Final.lean`. Do not substitute the Python partition for the Lean partition.
5. Run `python3 verify_release.py`; then compile the pinned public Lean package and execute `C13Global/AuditFinal.lean` as described in `lean/README.md`. Record whether upstream caches were used.
6. Distinguish proof correctness, historical transcription, finite search completeness, current compilation, novelty, and scholarly significance in any report. A successful checker run answers only its own question.

The central claim is the exact covering number. No claim is made to classify every optimum, settle a general family, re-prove the 1995 classification, or establish exhaustive worldwide priority.
