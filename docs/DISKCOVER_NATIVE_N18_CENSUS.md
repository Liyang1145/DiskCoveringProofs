<!-- SPDX-License-Identifier: MIT -->
# n=18 native Voronoi topology census

An arbitrary cover strictly below the [verified algebraic candidate](DISKCOVER_NATIVE_N18.md)
can only produce one of 14,559 canonical orbits in this screened census.
This is a quantified topology reduction, not a lower bound at the candidate:
the continuous center/anchor domains for the surviving orbits are not excluded.

## Arbitrary centers to a simple disk triangulation

Suppose \(r<r_*\) covers the unit closed disk using at most 18 centers.
Project centers onto the unit disk (all target distances weakly decrease) and
increase the radius to some \(\rho\) strictly between \(r\) and \(r_*\).
The strict slack permits a sufficiently small perturbation with all centers in
the open disk, distinct, and in general position. Exclude collinear triples,
cocircular quadruples, three-cell vertices on the unit circumference, and
bisector tangencies; these are finitely many proper algebraic conditions on
the centers. Remove redundant disks to obtain an inclusion-minimal cover.
Every remaining disk has a private point; that point is strictly closer to
its center than to any other center. Each clipped Voronoi cell is full
dimensional (the center is an interior point) and lies in its corresponding
disk because every target point is at distance at most \(\rho\) from some center.

**Non-return.** A clipped cell cannot have two components of its trace
on the circumference. Every disk's trace is a single short arc, of length
less than half a turn. If two trace points \(a,b\) belonging to one cell
are separated by an open omitted part of that short arc, the cap bounded
by \([a,b]\) and the intervening arc lies in that disk by convexity.
A point strictly between junctions in the omitted part belongs locally
to another full-dimensional cell. This second cell cannot cross the
bisecting chord line: convexity would give an interior point of the second
cell on \([a,b]\), which is contained in the first cell. Since a full
dimensional convex set is the closure of its interior, this would
contradict disjoint cell interiors. The second cell is therefore entirely
in the cap and hence in the first disk. Its private point forbids this.

A cell contacting the circumference without owning a positive-length arc
requires a clipped bisector tangency or a three-cell vertex on the
circumference, both excluded above. Add the exterior face on the sphere.
Each vertex now has exactly three incident cells. Distinct interior cells
meet along at most one shared edge by convexity; the non-return lemma gives
the same property for a cell and the exterior face. The dual is a simple
triangulation, whose exterior vertex can be deleted together with its open
star to yield a triangulated disk with \(b\) distinct boundary owners.
The intersections at interior triple-cell vertices supply three-center
witnesses, and junctions on the unit circle supply two-owner witnesses.
If fewer than 18 vertices survive, subdivide any triangular face by
adding an interior vertex, copying the center of one face vertex and
using its old witness for the three new faces. This preserves rod bounds
and \(b\). Repetition brings the disk triangulation to 18 vertices and
\(34-b\) faces without claiming the augmented graph is a geometric dual.

The circumference requires \(b\ge11\), using the single-disk half-angle
cap \(\arcsin(\rho)\) and the certified comparison
\(\sin(\pi/10)>U=0.290167718>r_*\). If \(b\ge14\), at least 14 disks
meet the unit circumference in the minimal subcover. Such disks cannot
meet the open concentric core of radius \(1-2\rho\); at most four other
disks must therefore cover the core, including its closure by finiteness.
The core circumference requires radius at least
\((1-2\rho)/\sqrt2\), which exceeds \(\rho\) because
\((1-2U)^2>2U^2\). Thus exactly the three ranges \(11,12,13\) require scanning.

## Exact angular pruning

In full-turn units consecutive anchors of a boundary owner have gap
less than \(9372/100000\). Join every witness to its incident centers.
A single center adjacency costs two rods, and each anchor is attached
to either of its two incident centers by one rod. Hence anchor pairs
whose endpoint-owner sets are at graph distance at most one or two
have witness paths of at most four or six rods, respectively. By the
chord formula their shorter angle separations are strictly less than
\(19708/100000\) or \(33621/100000\). The checker uses an exact
Machin lower bound for \(\pi\) and degree-15 rational alternating lower
bounds for sine at all three cutoffs to certify \(\sin(\pi c_k)>kU\).
These arguments apply to proper distances because all \(c_k<1/2\).

The peeler only uses installed center edges when inferring witness paths.
An oriented angle difference is constrained to be short only if its
forward arc cannot reach the long-arc threshold even using its maximal
number of owner gaps. If neither orientation can reach the long threshold,
both may be required short, which contradicts their sum of one. Every
constraint is therefore necessary for all completions of a discarded
partially installed graph. The root-face split counts both cases: a
third boundary vertex splits one region and allocates all possible
interior-vertex budgets, or the third vertex is a newly exposed interior
vertex. Each step installs one triangle, and all completions terminate
after the specified finite face count. The two traversals differ in
ordering and difference-constraint closure, but share the same C++ source
and canonical labeling.

## Fresh cross-replay

The repository source is bound by SHA-256
7063d6fbd45786696873b13c5d8b07e657bcdf47c685b0aae8392876373e53d0.
Read it from the Git object if the original directory is sparse:

    out=$(mktemp -d)
    git show HEAD:cover21/proof_bundle/research-2026/n21-global/peel21.cpp > "$out/peel.cpp"
    echo "7063d6fbd45786696873b13c5d8b07e657bcdf47c685b0aae8392876373e53d0  $out/peel.cpp" | sha256sum -c -
    g++ -O3 -std=c++17 "$out/peel.cpp" -o "$out/peel"
    for b in 11 12 13; do
      for mode in dfs audit; do
        "$out/peel" 18 "$b" "$out/$mode-$b.json" 100000 9372 19708 33621 0 "$mode" || exit
      done
    done
    python -B verification/n18/compare_census.py "$out"

| Boundary owners | DFS states | Audit states | Matched canonical orbits |
| ---: | ---: | ---: | ---: |
| 11 | 286,067 | 148,544 | 397 |
| 12 | 3,854,699 | 2,242,802 | 6,971 |
| 13 | 4,587,352 | 2,798,918 | 7,191 |
| Total | | | 14,559 |

The comparison verifies full face-table/stabilizer equality, exact orbit
accounting and canonical-orbit hashes rather than just these counts.
The 12-owner upper candidate's separately canonicalized face graph
is present, has stabilizer 2, and is included in the 6,971. See
[the receipt](../verification/n18/census_receipt.json).
