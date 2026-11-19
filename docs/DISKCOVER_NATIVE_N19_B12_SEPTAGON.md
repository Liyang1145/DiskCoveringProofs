<!-- SPDX-License-Identifier: MIT -->
# n=19: exact elimination of the one-interruption core septagons

**Scope.** For twelve positive-length boundary owners, this eliminates
all remaining census orbits in which six distinct core vertices are
assigned two boundary edges each. It does not eliminate any unspecified
multiplicity family or assert the global $n=19$ lower bound.

## Coverage of the discrete family

The [owner reductions](DISKCOVER_NATIVE_N19_B12_B13.md) prove that the
six doubletons are consecutive pairs. At each alternating transition
the link is direct or passes through the same seventh core vertex.
The [native census](DISKCOVER_NATIVE_N19_CENSUS.md) contains 11 orbits
with no interruption, 22 with one, and nine with two consecutive
interruptions. For the 11 zero-interruption and nine two-interruption
orbits the [lattice stress subgraph](DISKCOVER_NATIVE_N19_CANDIDATE_GRAPH.md)
is already present. In the latter, the seventh core vertex replaces
the leaf in the six-core cycle. For the 22 one-interruption orbits
the new proof below handles the full septagon. The verifier matches
all 22 certificate face sets to the exact census subset, and checks
the lattice subgraph presence for the other 20 cases.

## Rod graph and stress elimination

Normalize the target radius to 1. For each exterior switch use a
vertex $q_i$ on the unit circle linking to both adjacent owners.
For each triangular face use a witness vertex linking to all
three disk centers incident to the face. The witness is the
appropriate clipped Voronoi vertex. A real strict counterexample
at radius $r<1/\sqrt{13}$ gives such a graph realization with all
96 rod lengths at most $r$. In each orbit the data file supplies
a nonnegative integer weight per rod, normalized to sum to 1,
so its squared weighted rod energy is at most $r^2$.

Eliminate free vertices from the weighted energy by completing
the square: for incident weights $w_i$ with sum $s>0$, the
minimum over the eliminated vertex adds $w_iw_j/s$ between
each pair of its neighbors. A vertex without weight can be
skipped. This produces an exact nonnegative rational weight
$c_{ij}$ on each retained anchor pair. Every actual rod energy
is at least the reduced energy
\[
 E(\theta)=2\sum_{i<j}c_{ij}\bigl(1-\cos(\theta_j-\theta_i)\bigr).
\]
The certificate sample angles and rod weights were proposed
numerically and then rounded. They are arbitrary proof inputs,
not asserted stationary or optimal. No floating point, solver
status, or optimization results are trusted in the checker.

## A uniform lower bound over the anchor domain

Anchor gaps are nonnegative, sum to $2\pi$, and are at most
$2\arcsin(1/\sqrt{13})<D=.562071$, because each pair of successive
switches lies in one short owner arc. Fix $\theta_0=0$. The
checker verifies that each rational expansion point $x$ is in
this same enlarged gap domain, including the cyclic closing gap.
In particular every line segment from $x$ to a candidate $\theta$
stays inside the enlarged domain.

For a pair with $d=j-i$, its angle difference lies in
\[
 [\,2\pi-(12-d)D,\ dD\,].
\]
On the entire segment, its cosine is at least
$\cos(kD)$ if $k=\min(d,12-d)\le5$, since the shorter **index**
path has length at most $kD<\pi$; for $k=6$, use $-1$.
Taylor's formula therefore bounds the pair's contribution below
by its value and linear term at $x$ plus
$c_{ij}b_k((\theta_j-\theta_i)-(x_j-x_i))^2$, where $b_k$ is the
verified cosine lower bound. Drop that quadratic contribution
when $b_k\ge0$. For a negative $b_k$, use the squared maximum
distance from $x_j-x_i$ to the two endpoints of the above
interval, using a lower approximation of $\pi$ in the first
endpoint. The result is a uniform lower bound on the full
Taylor remainder; it does not claim convexity of $E$.

Let $g$ be the resulting rational approximation to the angle
gradient at $x$. The verifier gives a directed error bound for
each pair's approximate sine derivative times its variation
(in absolute value below 7). For the linear term, write the
gap coefficients as the suffix sums $p_i=\sum_{j>i}g_j$, with
$p_{11}=0$. Then $g\cdot\theta=\sum_i p_i\,\Delta_i$.
Writing $\Delta_i=D-s_i$ shows
\[
 g\cdot\theta\ \ge\
 D\sum_i p_i-(12D-2\pi)\max_i p_i
\]
because the $s_i$ are nonnegative and sum to $12D-2\pi$.
The upper bound on this total slack from the lower approximation
of $\pi$ is safe since $\max_i p_i\ge p_{11}=0$. Subtract
$g\cdot x$, the derivative error and the curvature loss, then
add the directed lower bound for $E(x)$. The checker does all
these operations with Python fractions. Its scalar sine and
cosine enclosures use rational Taylor polynomials with the
absolute Lagrange remainder bound and outward rounding; its
$\pi$ interval is verified by Machin's identity and rational
arctan bounds.

Across the complete 22-orbit septagon family, the certified uniform
lower bound on squared radius is at least $.080329$, strictly
greater than $1/13$. It contradicts any strict counterexample.

## Replay and source binding

After regenerating the B12 census according to the
[census instructions](DISKCOVER_NATIVE_N19_CENSUS.md), run:

```sh
python verification/n19/check_septagon_force.py /path/to/dfs-12.json
```

The normalized DFS orbit list must match SHA-256
`afa40b377df80ff65d032dd899f28c30065dc0b1ad0fcd2402483435a3d2d446`.
The [rational stress data](../verification/n19/septagon_force.json)
have SHA-256
`a94588e0aa81bb1c3e4af27f14a6bd09d9c7061a9a8fe2e24968be82f6051d20`.
The verifier rejected a removed certificate and an all-zero weight
mutation in addition to accepting the full run.
