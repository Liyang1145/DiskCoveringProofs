<!-- SPDX-License-Identifier: MIT -->
# Public verification layer: fresh results on 2026-10-14

## n12: complete k10 arithmetic, not a new unrestricted global replay

Executed on Windows with Python 3.14 and NumPy:

```sh
python tools/mathcheck_n12.py --workers 8 --report publication-local/n12-full.json
```

The run freshly recomputed exact FGHT root isolation, the complete original
hub-domain binary partition, all **318** infeasibility predicates and all
**6723** atomic inequalities: **7041** terminals, **zero cache hits**,
**69,946,711** ring-center boxes, minimum integer gap **6**. It completed in
**1035.355 seconds** and emitted `N12 FULL K10 MATH REPLAY PASSED`.
The three prune families had 20, 111 and 187 terminals. The last family
also passed exact integer-square-root crosschecks.

The [full compressed report](../verification/public-math/n12-full-20261014.json.gz)
includes one fresh result per atomic leaf and hashes of the executed source
and all small input files. It is an execution record, not an accepting input
to future runs. The new checker never reads this report or an old verdict.

## n11: explicitly scoped fresh arithmetic

`python tools/check_math.py n11` passed root isolation, same-root threshold,
interval candidate geometry and all **371** Schur stress fields with
**13,356** exact pair weights. The [report](../verification/public-math/n11-scoped-20261014.json)
records `SCOPED_PASS` and `full_global_proof_replayed=false`. See
[N11_CHECK_SCOPE.md](N11_CHECK_SCOPE.md) for the unreplayed source obligations.
The checker also passed with Python optimization enabled.

## Portability and rejection controls

Both entry points passed in a separate directory containing only the new
tools and `math_data`, including spaces and Unicode in its path. No archived
proof bundle, original workstation path, Git state, network or historical
verdict cache was required. A quick n12 run with `--require-global` failed
as intended and did not emit a mathematical acceptance marker.

Thirteen mathematical rejection controls passed in ordinary and optimized
Python modes. They include a forged FGHT equation, singular preconditioner,
missing/duplicated partition terminal, pending domain, invalid core witness,
nonunit circle vector, unsafe integer scale, zero demand and perturbed n11
root. The delivery corruption/no-overwrite controls also passed; their
subprocess output now explicitly uses UTF-8 on Windows.

The gallery passed deterministic regeneration, source hashes, coordinate
and radius checks, SVG parsing and rendering. It contains **84 centers** in
**five** drawn configurations and an **eight-order** radius index.

A separate read-only review of the n12 equations, interval contraction,
closed partition, pruning signs, screening, int64 guards and report scope
found no bearing arithmetic issue. This review was not a second implementation
of the complete atomic replay. External mathematical review remains separate.

Original source-proof files and historical acceptance evidence are preserved.
The original delivery manifest is archived byte-for-byte under
`manifests/history/`; maintained documentation and new portable assets receive
current hashes in the live manifest. No global proof status is upgraded by
this release, and n26 remains explicitly incomplete.
