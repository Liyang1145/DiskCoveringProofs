# n=26 continuation synchronized 2026-11-08

The continuous research goal is PAUSED at the user's request. This publication
archives existing progress and the newly requested external-proof review.

The current independently checked bounds are `0.229 < r_D(26) <= rho`, with
`rho < 0.234700090400448239616790133776693`. The exact root definition and
same-root cover are in [round b](workspace/round-20261107b/PROOF.md).
No unrestricted matching lower bound is claimed. Native formal 16 roots,
4957 conditional prefixes, and arithmetic 344 OPEN domains remain unpaid.

- [Current status](workspace/STATUS.md).
- [Global lower bound 0.229](workspace/round-20261107/PROOF.md).
- [Triangle shape lemma](workspace/round-20261107c/PROOF.md).
- [General-cover geometry interface](workspace/round-20261107d/PROOF.md).
- [Paused arithmetic checkpoint](workspace/round-20261107e/REPORT.md): 29 exact
  kernels, 2999 reconstructed nodes, all 344 original OPEN domains, four new
  conditional kernels, eight FAILED whole-domain margin attempts, zero payments.
- [External n11/n14 review](../../../external-submissions/2026-11-08-sol-review/REVIEW.md).

Restore compressed workspace inputs from the committed, hash-bound parts:

```sh
python cover26/continuations/2026-11-08-terra/restore_workspace.py
python cover26/continuations/2026-11-08-terra/workspace/round-20261107b/replay.py
python cover26/continuations/2026-11-08-terra/workspace/round-20261107c/replay.py
python cover26/continuations/2026-11-08-terra/workspace/round-20261107d/replay.py
python cover26/continuations/2026-11-08-terra/workspace/round-20261107e/checkpoint_replay.py
```

Python 3.10+ and Node are required for the bound/shape replays; round d's
symbolic interface additionally uses SymPy. The checkpoint acceptance uses
the Python standard library. NumPy/SciPy/SymPy/mpmath/ijson are proposal or
extraction dependencies, not cached verdicts for the checkpoint acceptance.
The historical full ledger, old SYSTEM identity, and geometric joint acceptance
have NOT been replayed. Existing huge current snapshots are reused by byte alias;
the original public parts are neither modified nor uploaded again.

The earlier unpublished October 29 and 30 continuations are also included in
their dated directories. Failed experiments and original source qualifications
are preserved. Original source rights and third-party attribution are retained.
