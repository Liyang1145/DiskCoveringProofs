<!-- SPDX-License-Identifier: MIT -->
# Fresh arithmetic verification

The new entry points run independently of the original Windows/WSL workspace.
They read only `math_data/n11/` or `math_data/n12/`, require no login, and do not
read historical acceptance verdicts. Restoring the large archived delivery is
unnecessary for these entry points. Python 3.10+ and NumPy suffice; n11 itself
needs only Python's standard library.

```sh
python -m pip install -r requirements-math.txt
python tools/check_math.py n11 --report build/math-n11.json
python tools/check_math.py n12 --workers 4 --report build/math-n12.json
```

`make check-math-n11` and `make check-math-n12` run the same commands.
`python tools/test_math_checks.py` tests rejection of corrupted equations,
singular root matrices, missing/duplicate terminal boxes, pending domains,
nonunit vectors, unsafe integer scales, zero demand and a perturbed n11 root.
No source certificate is modified by these tests.

## Twelve disks: all 7041 k10 terminals

The checker freshly computes the four-polynomial rational Krawczyk contraction
and strict self-map, verifies that the exact radius lies below the rational
k10 threshold, reconstructs the complete closed binary hub partition, and
rechecks all 318 infeasibility predicates. The 187 radical predicates are also
checked using exact integer-square-root enclosures.

Each of the 6723 other terminals is checked without a verdict cache. Exact
rational circle vectors and nonnegative integer weights define an atomic
measure. The checker rebuilds outward integer atom rectangles and subdivides
the whole ring-center square. A rectangle is removed only by the necessary
annulus tests or a capture bound satisfying **10 M < T**. Equality fails.
Both closed children of each dyadic split are retained. Unsupported vector
counts, overflow scales, exhausted search or unresolved rectangles fail.

NumPy accelerates integer arithmetic only. Explicit endpoint and positive
weight-sum guards ensure every squared distance and sum fits signed int64.
The original weight proposals and scale exponents are witness parameters;
the demand, maximum capture and strict gap are recomputed. No saved gap,
stored PASS flag, solver optimum or floating-point distance is a premise.

The full marker is `N12 FULL K10 MATH REPLAY PASSED`. Use `--quick` on the
unified entry point or `--limit` on `mathcheck_n12.py` for a sample; samples
never emit the full marker. Full execution may take several minutes to tens
of minutes, depending on hardware and worker count. Reports contain actual
elapsed time, fresh atomic count and subdivided ring-box count.

## Eleven disks and the global proof

The n11 checker recomputes the boxed 12-dimensional stationarity root,
same-root threshold, interval configuration geometry, and every exported
positive-stress Schur field. See [the precise scope](N11_CHECK_SCOPE.md).
It does not replay all global angular leaves or the two-circle capacity
partition. Its success marker is deliberately `SCOPED`, not global.

The n12 full k10 branch is also only part of the unrestricted global source
proof. The analytic cover-to-domain reduction, k9/k11 arguments and ideal
whole-disk attainment remain in the archived source chain. Neither command
certifies a complete new formalization or substitutes for external review.
`--require-global` fails while these obligations are outside the execution
scope, even after all included computations succeed.

Delivery integrity remains separate: `python tools/verify_delivery.py`
checks the original byte manifest, while `restore_large_files.py` restores
archived dependencies. Original proof-bundle bytes and their manifest entries remain unchanged.
The original manifest is retained byte-for-byte in `manifests/history/`;
the live manifest tracks updated maintained documents and new assets. The new small input snapshots have their own provenance records.

CI runs mathematical rejection controls, n11 arithmetic and a labelled n12
sample on each change. Its manual workflow can request the complete n12
replay and uploads fresh reports. Sample CI is never advertised as a complete
global mathematical acceptance.
