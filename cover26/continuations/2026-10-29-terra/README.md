# n=26 supplemental bounds, 2026-10-29

Fresh rational computations and the written geometric arguments establish

    2/9 < r_D(26) <= 234700091/1000000000 = 0.234700091.

Here 26 arbitrary plane centers, repetitions, tangencies and redundant disks
are allowed in the lower bound. The upper bound is a specific rational cover.
This supplement does not establish the exact optimum, identify the old
isolated root with these decimal-grid coordinates, or close the native
formal/arithmetic frontiers. No originality or priority claim is made.

Run with Python 3.10+ and its standard library:

```sh
python cover26/continuations/2026-10-29-terra/replay.py
```

The lower proof uses weighted angular measures on 15 concentric circles.
Two arithmetic implementations bound the entire center-distance domain in
4400 closed intervals, using cosine and arctangent inequalities respectively.
See [the lower proof](lower/proof.md). The upper proof is replayed both by
restricted Voronoi extrema and by an oriented triangular complex; see
[the geometric proof](upper/triangulated-proof.md). Fresh replay recomputes
the inequalities and never accepts saved PASS flags.

Coordinates are credited to pikachu345, MinMax Arena P87/n26, whose page
records the construction on 2026-10-05:
https://minmaxarena.com/en/problems/circles-cover-disc/p87-n26-v1
The source data are CC BY 4.0; original and translated coordinates and
attribution are in upper/PROVENANCE.json. Translation subtracts (1,1).
Do not attribute the source construction to this continuation.

The same grid coordinates fail at 0.234700090, with an exact uncovered
witness. Their required radius also exceeds the saved candidate-root upper
endpoint; they therefore cannot replace a same-root attainment certificate.

The boundary14 notes supply only necessary norm counts and document why
one earlier sufficient area exclusion does not apply. They do not exclude
the B=14 family. The original 16 formal roots, 4957 conditional prefixes and
344 arithmetic OPEN subdomains are unchanged. Native input closure and
unrestricted global composition are still unpaid.

REPLAY.json records the actual executions of this supplement, with source
hashes. It is an execution record, not an acceptance premise. The existing
proof files and frozen receipts are unchanged. The commit was prepared on
the latest locally available base; no claim about a newer online head is made.
