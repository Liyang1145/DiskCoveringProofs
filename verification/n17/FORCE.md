<!-- SPDX-License-Identifier: MIT -->
# n=17: native force certificates after the topology census

The checker uses this repository's n=19 force construction, the native
n=17 census, and the rational n=17 constructive upper bound. It does not
execute or import an upstream checker, enumerate an upstream asset, or
read upstream acceptance flags.

For a strict improvement, choose a checking radius between its radius
and the exact algebraic candidate radius, not merely below the rounded
rational upper bound. Apply the native Voronoi reduction and interior
padding at that intermediate radius. Each admissible triangulation has
boundary anchors of norm one, each incident to its two owners by rods.
Each central triangle supplies a face witness linked to its three
centers by rods. All rods in this necessary realization have length
strictly below the candidate radius and hence below the slightly larger
rational test bound `U`.

The angle roots use the closed ordered angle domain, with one anchor
fixed at `(1,0)`, and tighten it using the proved rational angular caps.
Each split is an exact closed bisection of a single angle, with endpoints
overlapping intentionally. Negative cycles and inverted tightened
intervals do not certify a force inequality: the separate empty leaf
requires its own exact interval contradiction.

At a force leaf, the certificate is an integer edge flow and a
nonnegative multiplier at each nonfixed anchor. Each interior node has
zero divergence exactly. Rotationally fixed anchor 0 contributes a
constant; at every other anchor, an enclosing arc provides a rational
linear support inequality. Summation by parts converts anchor work
into edge work. Applying Cauchy--Schwarz to each rod upper-bounds the
latter by `U * sum(norm(flow))`; the checker uses integer-square-root
upper bounds and tests a strict reverse inequality against the lower
bound on the former. Arc directions are enclosed by rational Machin and
Taylor bounds. The floating LP proposes leaf data only and is not part
of acceptance.

## Replay

```sh
python tools/check_native_n17_census.py --output-directory /tmp/n17-census
python verification/n17/replay_force.py /tmp/n17-census verification/n17/runs/*-force.json
```

Supply `--require-complete` for a full noncandidate completion check;
otherwise the script must be read together with its explicit unresolved
orbit list. It rejects wrong graph-to-index binding, duplicates and any
incorrect leaf. A noncandidate completion check does not establish
the candidate branch.

The standalone candidate code matches the original oriented face
labels, checks all their possible dihedral stabilizers and interior
relabelings, and replays local leaves against the independently
accepted anchor isolation result. The second distinct placement pins a
different original anchor. Before measuring the displacement, its
local test subtracts the uncertain pin angle from each actual angle and
the corresponding reference pin angle from each reference angle; the
sum of squared turn differences, scaled by `(2*pi)^2`, bounds total
Cartesian displacement squared. Passing that local bound applies the
isolation theorem to a strict-improvement realization at the smaller
radius, not at `U`. The force leaves remain checked against `U`.
The presence of the candidate code alone does not certify the
candidate-domain complement.

The optional extra directed chord support has an independent exact check.
For ordered anchor angles $s_i,s_j$ in turns with $i<j$, write
$d=s_j-s_i$. Their directed chord is
$2\sin(\pi d)$ times the unit tangent at the average angle.
Angular difference constraints and interval bounds give a closed
subinterval for $d$; the sine minimum there is at an endpoint by
concavity on $[0,\pi]$. Dotting the tangent with the tangent at the
midpoint of its possible arc multiplies by a cosine whose lower bound
is computed at the maximum deviation. The checker rounds that reference
tangent to a rational vector and subtracts an error bound using chord
length at most two. A nonnegative multiplier of the resulting chord
inequality can be added at a force leaf. Its contributions at the two
anchors have opposite signs, and the fixed-anchor translation terms
cancel. Using these extra inequalities is optional; old leaves without
them still replay.

## Depth-9 checkpoint

Fresh native exact-force generation and verification paid these
noncandidate branches (zero-based indices in the native census):

| Boundary owners | Paid / total noncandidate | Unpaid |
|---:|---:|---|
| 11 | 489 / 489 | none |
| 12 | 623 / 630 | 612, 616, 621, 622, 624, 628, 630 |
| 13 | 196 / 200 | 169, 170, 198, 199 |

The accepted certificates are in the first-pass and depth-9
`runs/*-force.json` files. Their corresponding generation reports
distinguish the attempted sets and the depth-limit failures. A depth limit
does not imply feasibility, and these counts do not include the one
candidate orbit. The scalar-force candidate generation at depth 18
stopped at an unresolved angle box and yielded no accepting tree.

## Original-gauge numeric witness replay for the candidate

The separate `candidate_data_replay.py` checker accepts no upstream
programs, supplied support offsets, or summary verdicts. It takes only
the fixed compressed numeric tree, and checks the ordered 20 faces and
84 rods against the original candidate and its independently matched
native census orbit. Its redundant, slightly larger angular caps
96500 / 203670 / 353250 in millionths of a revolution are verified
again before they are used. Every split reconstitutes its closed
children and every leaf is independently checked. Exact rational
point/trigonometric enclosures bound each whole local arc's maximum
squared displacement in the original gauge, not merely its midpoint.
Acyclicity, exact reachability, integer force divergence and strict
force separation are mandatory.

```sh
pin=089584973f41e6374ce110f6e5b5ee456df19352
curl --fail --location --output /tmp/n17-candidate-tree.json.gz "https://raw.githubusercontent.com/VonEquinox/DiskCoveringSolve/$pin/cover17/proof_bundle/core/candidate17_tree.json.gz"
python verification/n17/candidate_data_replay.py /path/to/root17.json /tmp/n17-census/n17-B12.json /tmp/n17-candidate-tree.json.gz --negative-controls
```

The compressed input SHA-256 is
`a0b2b799879f290898c6d3d15dcf745611f99cf1ff5e9f05e8ea147ec403e3e9`.
The standalone candidate tree applies only after relabeling a competing
embedding to the original candidate faces and choosing the corresponding
original anchor zero as the rotation/reflection gauge. It never assumes
canonical census anchor zero matches that anchor.

## Complete native replay

The baseline generated archives in `runs/` are exactly
`B11-force.json`, `B12-force.json`, `B12-deep-force.json`,
`B13-force.json`, `B13-deep-force.json`, `B12-pairs-force.json`, and
`B13-pairs-force.json`. With these seven archives only B=12 IDs 612
and 628 remain. They were independently relabeled to two rows in the
fixed external numeric forest. The relabeling exhausts cyclic shifts,
cycle reversals, and interior permutations preserving graph degrees
then compares full triangle masks; invariant prefilters alone do not
certify matching. Every matched row is checked over its entire root
angle domain with native rational arithmetic. The replay ignored
the source summary verdicts, chart offsets and all non-matching trees.

```sh
pin=089584973f41e6374ce110f6e5b5ee456df19352
base="https://raw.githubusercontent.com/VonEquinox/DiskCoveringSolve/$pin/cover17/proof_bundle"
curl --fail --location --output /tmp/n17-root.json "$base/core/root17.json"
curl --fail --location --output /tmp/n17-candidate-tree.json.gz "$base/core/candidate17_tree.json.gz"
curl --fail --location --output /tmp/n17-noncandidate.jsonl.gz "$base/enumeration/noncandidate17_trees.jsonl.gz"
python verification/n17/check_global.py /tmp/n17-root.json /tmp/n17-candidate-tree.json.gz /tmp/n17-noncandidate.jsonl.gz
```

The numeric forest digest is
`0bb19fb51bf7a9d99f9b149d5040352200138e46b288383d17c2a6dce973cb1d`.
The integrated checker regenerates the topological census, replays the
seven generated files, rechecks the two numerical trees and the original
candidate tree, verifies exact attainment and isolation for the same
root, and rejects gaps or duplicate coverage in the orbit inventory.
It needs Python 3.10+ and a C++17 compiler, and does not require SciPy.
The exact geometric reductions supporting the calculation are in
[the native n=17 proof](../../docs/DISKCOVER_NATIVE_N17.md).
