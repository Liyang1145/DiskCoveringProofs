# n=26 continuation: strict lower bound 28/125

Date: 2026-10-30 (client timezone Asia/Shanghai).

Freshly replayed rational arithmetic and the accompanying written argument give

    28/125 < r_D(26) <= 234700091/1000000000.

The upper bound is the previously replayed MinMax Arena construction in
../2026-10-29-terra/upper/. This round improves the unconditional lower bound
from 2/9 to 28/125. It does not determine the exact optimum.

Run `python cover26/continuations/2026-10-30-terra/replay.py` with Python 3.10+.
Acceptance programs use only the standard library. Optional proposal/solver
code may require SciPy; it is not a mathematical acceptance premise.

## Accepted scope

- Global lower bound: 56 nonnegative weighted concentric circles, 24480 closed
  center-distance cells, and at least one disk containing the origin. The
  latter disk's weighted capacity is strictly below the universal maximum.
  The cosine and independent arctangent implementations both give a strictly
  positive exact rational gap. See lower/REPORT.md and audit/.
- At the FIXED radius 9/40, covers with exactly 14 or 17 disks meeting the
  unit circle are impossible, checked by both arithmetic implementations.
  Elementary boundary/core inequalities leave only B=15 or B=16. For a smaller
  radius, first enlarge all disks to 9/40 and THEN classify B: the number of
  boundary-intersecting disks need not be preserved by enlargement.
- Referencing the published eight-disk theorem of Gabor Fejes Toth (2005),
  arbitrary covers of radius at most 0.234700091 have 14<=B<=17 and at least
  nine nonboundary disks. This theorem is cited, not newly proved here:
  https://library.slmath.org/books/Book52/files/18fejes.pdf . B counts actual
  boundary intersections; it is not automatically a Voronoi-cell count.

## Conditional or unresolved work

The geometry/ results require the explicitly stated boundary-ownership and
triangulated-area interface. They give stronger lens/area necessities and an
exact obstruction to treating all lenses and all face areas independently;
they do not exclude the entire B14 branch at the candidate radius.

The finite-witness protocol enumerates possible disk-capture patterns using
exact pair-circle intersections. A 241-point example is rigorously covered
by 23 disks, so it is too weak to exclude 26. A denser 1361-point numerical
instance hit its time limit and remains unverified/PENDING. The tiny abstract
set-cover example only validates the branch-certificate interface. None of
these facts closes a full-disk covering problem at radius 9/40.

The native 16 formal roots, 4957 conditional prefixes and 344 arithmetic OPEN
subdomains remain unpaid by this supplement. Exact candidate-root identity,
full catalogue, unrestricted geometric composition and frozen-input closure
remain necessary for the requested optimum proof. No complete theorem,
originality claim, external review or formalization is asserted.

REPLAY.json contains fresh outputs, input hashes and exact scope. Saved PASS
flags are never read as premises. Existing frozen proof bytes are unchanged.
