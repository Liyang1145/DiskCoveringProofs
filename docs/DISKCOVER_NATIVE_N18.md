<!-- SPDX-License-Identifier: MIT -->
# n=18: native two-circle lower bound and rational construction

Fresh independent checks certify the interval
\[
  0.26590 < r_D(18) \le
  0.290167717640566729113154525601061718306280885754041798808099.
\]
The gap is not closed. Neither inequality relies on an external proof's
acceptance marker. The upper construction uses external coordinate data as a
seed only. The lower bound has no candidate premise.

## Arbitrary-center lower bound

Work at test radius \(r=0.26590\). Any cover at a smaller radius can be enlarged
to radius \(r\) with the same centers. Count **all** disks meeting the unit
circumference as \(B\), including tangencies; covers with fewer than eighteen
disks can be padded by duplicates.

The [one-circle estimate](DISKCOVER_NATIVE_N17.md) implies \(B\ge12\):
each of at most eleven disks would cover half-angle at most
\(\arcsin r<0.28<\pi/11\). If \(B\ge13\), the at most five other disks have
to cover the closed disk of radius \(1-2r\) by the same core-peeling lemma.
Already its circumference requires radius
\((1-2r)\sin(\pi/5)>r\). This leaves \(B=12\) only.

Take the additional concentric test circumference at \(t=0.58670\).
Writing \(A_u(d)\) for a disk of center norm \(d\)'s covered half-angle on
the radius-\(u\) circle, use weight \(w=39/50\) on the unit circumference
and \(1-w\) on the inner one. Covering both requires the sum of the
eighteen weighted half-angles to be at least \(\pi\), by subadditivity
of lengths on each circumference separately. Each of the six disks
not meeting the unit circumference contributes at most
\((1-w)\arcsin(r/t)\).

For the other twelve disks, \(d\in[1-r,1+r]\). For both \(u=1\) and
\(u=t\), the covered angle is zero when the cosine-law ratio
\((u^2+d^2-r^2)/(2ud)\) is at least one, and otherwise it is the arccosine
of that ratio. The ratio is positive throughout the checked radial range.
Partition that range into closed intervals \([a,b]\) of width \(10^{-5}\).
On each interval the positive ratio is bounded below by
\[
 (u^2+a^2-r^2)/(2ub).
\]
Choose an angular upper bound on the \(10^{-5}\) grid by comparing this
lower ratio to the alternating degree-eight **upper** Taylor bound for the
cosine. Combine the two upper bounds for the **same** radial interval before
maximizing, rather than maximizing the two circles independently. The
Python checker performs the 53,180 interval calculations with integer
arithmetic. It certifies an exact weighted sum upper bound of
\(7851033/2500000 = 3.1404132 < \pi\), a contradiction. The comparisons
for all three cases use rational alternating-series bounds, including a
Machin lower bound for \(\pi\).

This gives a strict inequality for the minimum, not just infeasibility
at a test radius: radial projection of every center onto the closed unit
disk cannot increase its distance to any target point in that disk.
The covering radius as a function of the ordered centers is continuous
(in fact 1-Lipschitz in the maximum center displacement). Hence an optimal
configuration exists by compactness, and cannot have radius at most the
excluded rational value.

## Rational upper construction

The eighteen centers are public [root-box midpoint coordinates from the
pinned external source](https://github.com/VonEquinox/DiskCoveringSolve/blob/089584973f41e6374ce110f6e5b5ee456df19352/cover18/proof_bundle/core/root18.json),
coordinates 22 through 57 in zero-based \(x\) order, each rounded to the
nearest multiple of \(10^{-60}\). The source file's SHA-256 is
`446d47409d67bd6d6d2af39813b6c4b974f29d896ea8b25f7ec15bf78dd13c34`.
The verifier treats these **rounded rationals** as exact centers. It does
not claim localization, uniqueness, or exact attainment by an algebraic
root.

With all coordinates integer-scaled, discard a closed square only if its
exact minimum distance from the origin exceeds 1. Alternatively, certify
coverage when the farthest corner from one center is within the radius.
Otherwise subdivide it into four children covering their parent. Exhaustion
of the depth budget is an error, not an acceptance. The replay finds
49,725 nodes: 6,528 outside, 30,766 covered, and 12,431 split, through depth
199. It also rejects a radius of 0.29 for these same rational centers.

Run offline from the repository root:

```sh
python -B tools/diskcover_n18_lower.py
python -B tools/diskcover_n18_upper.py
python -B tools/test_diskcover_n18_lower.py
python -B tools/test_diskcover_n18_upper.py
```

## Independent exact algebraic upper bound

The separate polynomial checker proves that the specified isolated root
itself supplies a cover:
\[
 r_D(18)\le r_*:=\sqrt{t_*},\qquad
 0.290167717640566729113154525601061718306280885754041798808094
 <r_*<
 0.290167717640566729113154525601061718306280885754041798808095.
\]

Save the hash-pinned root18.json data file linked above and run this
command from the repository root. No external executable or stored
verification verdict is used.

    python -B tools/diskcover_n18_algebraic.py path/to/root18.json --negative-controls

The verifier reconstructs the 72 rod equations, eleven anchor norm equations,
and 91 stationarity equations by their monomials. For the complete polynomial
map \(F\) and supplied rational preconditioner \(Y\), it uses the exact
displacement term \(|YF(x_0)|/\rho\), derivative-row errors \(I-YDF(x_0)\),
and a bound for derivative variation on each box of half-width \(\rho =
10^{-60}\) and \(10^{-80}\). A quadratic monomial with coefficient \(c\)
contributes at most \(2|c|\rho\) to the derivative row variation in the
one-norm, also for a repeated variable. The sum of the three terms is
strictly less than one in every row. Thus \(x\mapsto x-YF(x)\) is a
strict contraction sending each closed box inside itself. The matrix
\(Y\) is invertible since \(\|I-YDF(x_0)\|_\infty<1\). The fixed point
therefore zeros the 174 equations, and uniqueness with nested boxes
identifies the same root. The 72 contacts and unit-anchor constraints
are exact there.

For each active center triangle the incident rods give a common point
\(p\) at distance \(r_*\) from its centers \(c_j\). For
\(x=\sum_j\lambda_j c_j\) with nonnegative weights summing to one,
\(\sum_j\lambda_j\|x-c_j\|^2=
\sum_j\lambda_j\|p-c_j\|^2-\|x-p\|^2\le t_*\).
Thus every point of the triangle belongs to at least one center disk.
For the six inactive center triangles, the midpoint circumcenters are
rational witnesses with strictly greater squared-distance slack than
\(303/250000\) throughout the root box, so the same argument applies.

For each boundary center there is one outer triangle with both unit
anchors in its disk and one triangle with the common anchor shared by
two disks. All 46 triangles are strictly positively oriented and their
directed boundary sum is exactly the boundary chain of the strictly
convex anchor polygon. Additivity of winding number gives coverage
off the triangle edges, and closedness extends it to all polygon points.

The verified interval signs also say that each short boundary arc has
length \(<\pi/2\) in angle and contains the direction of its corresponding
center. The squared distance to that center is maximized at an arc
endpoint, both exact rod contacts. The convex disk therefore contains
the whole arc and its circular cap. The polygon and the twelve caps
cover the unit disk. All sign, slack and acceptance decisions use
exact rational arithmetic. Negative controls reject a corrupted
preconditioner, invalid center direction, and incorrect radius.

## Remaining global proof

At the candidate scale the native peeling argument still allows 11, 12,
or 13 boundary disks. The arbitrary-center Voronoi reduction and
exhaustive continuous exclusion of the surviving types must still be
paid, including strict exclusion below the candidate within its own
topology. The isolated-root and exact-attainment check supplies the upper
half of the exact-radius argument only. The strict native lower bound
remains \(0.26590\), not \(r_*\).

The boundary anchor $q_0$ is also checked to be strictly farther than
$\sqrt{t_*}$ from every nonincident disk center. The two incidence rods
have length $\sqrt{t_*}$, so the radius for this fixed configuration is
exactly $\sqrt{t_*}$; this does not prove optimality over all configurations.
