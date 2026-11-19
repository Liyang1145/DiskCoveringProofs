<!-- SPDX-License-Identifier: MIT -->
# n=19: complete native graph-to-force exclusion

This is the continuous exclusion stage of the native exact lower proof,
not a search for a smaller covering and not a reuse of the reference
author's certificates. No assumption of symmetry or proximity to the
attaining configuration is made for arbitrary covers.

## From smaller-radius covers to the census

Write \(R=1/\sqrt{13}\). A cover with radius \(r<R\) has a uniform strict
margin at radius \(R\). The [normalization and owner argument](DISKCOVER_NATIVE_N19_B14.md#how-contact-count-and-owner-count-interact)
allows all sites to be distinct generic points with norms
strictly below \(\sqrt{1-R^2}\). It proves that each positive boundary
owner has just one arc and that there are 12, 13 or 14 such owners.
An actual disk–circle contact need not be an ownership arc.

Every center is in the interior of the target and in the interior of its
own clipped Voronoi cell, so no center disappears. Cell intersections
are convex. On the sphere with the exterior as an extra cell, generic
vertices meet exactly three cells, and two cells share at most one edge
(the interior–exterior case follows from the connected owner arc).
The resulting dual is a simple sphere triangulation. Removing the open
star of the exterior vertex leaves a disk triangulation with 19 sites,
\(B\) boundary sites, and \(36-B\) faces. The order of its boundary sites
is the order of owner arcs. For each face take its interior Voronoi
vertex, and for each boundary edge take the unit-circle ownership
switch. Join these auxiliary points to the three or two incident sites.
Each rod length is strictly below \(R\), by strict coverage and nearest
ownership. In particular the consecutive boundary switches belong to a
common covering disk. Their short forward angle differences sum to one
turn.

The local configurable peeling census (the repository's `peel21.cpp`,
run with `N=19`) enumerates the graphs of this scope. Root each pending
polygon along an edge. Its unknown incident face has a third vertex
either already on that polygon, splitting the region with every
possible allocation of the interior budget, or unexposed inside it,
decrementing the budget and adding a new boundary vertex. Label fresh
vertices in exposure order. A new edge cannot duplicate an already
installed nonboundary edge. The number of remaining faces decreases
by one at each step (a polygon of size \(p\) with \(k\) inner sites has
\(p+2k-2\) remaining faces). An actual completed triangulation determines
a unique root-face choice and budget at each step and hence survives
this exhaustive generation up to labeling if it passes the necessary
angle conditions. Canonicalize by rerooting each of the \(2B\) directed
boundary edges and assigning inner labels by deterministic face
traversal. All these transformations are allowed by rotation, reflection
and relabeling of a realization.

Here \(U=27735009811263/10^{14}>R\). A forward gap is at most
\(A=8946/100000\) turns; 4- and 6-rod anchor paths imply corresponding
differences \(v\) in \(v\le C\) or \(v\ge1-C\), with
\(C=18717/100000\) and \(31284/100000\), respectively. These caps follow
by comparing the longer test radius \(U\) to respectively
\(\sin(\pi A)\), \(\sin(\pi C)/2\) and \(\sin(\pi C)/3\),
checked by directed arithmetic. The long alternative is discarded only
when the relevant \(k\)-gap forward span has \(kA<1-C\);
the complementary direction is handled by the same rule. Thus partial
graph screening by a negative cycle in the integer difference bounds
cannot lose a true completion. The two local census traversals must
agree on the **whole** set of canonical face lists and stabilizer counts,
not just the number of graphs.

## Exact continuous certificates

Fix the first anchor \(q_0=(1,0)\). The root box for all other turn
coordinates is \([0,1]^{B-1}\). The verifier independently reconstructs
and closes the graph's difference constraints, then intersects each
coordinate interval with all resulting necessary bounds. A split only
uses a strict interior rational cut and both closed halves. No search
failure or optimizer status can be accepted as a proof leaf.

For every arc interval \([\ell_i,h_i]\), let its exact midpoint unit
normal be \(a_i^*\). The entire arc satisfies
\(a_i^*\cdot q_i\ge\cos(\pi(h_i-\ell_i))\). The checker uses
Machin's formula and a Taylor remainder enclosure to derive a rational
normal \(a_i\) and a rational lower support \(c_i\), subtracting an upper
bound on the normal's coordinate errors. Therefore
\(a_i\cdot q_i\ge c_i\) for every possible anchor in that interval.

A force certificate supplies rational flow vectors \(f_e\) on the
oriented rods and coefficients \(\mu_i\ge0\). The checker recomputes
divergences, requiring zero at every unanchored site and every face
witness. Let \(F_i\) be the divergence at the \(i\)-th anchor and
\(d_i=\mu_i a_i-F_i\). At any realization of these anchor intervals,
\[
\begin{aligned}
\sum_e f_e\cdot(z_{\rm tail(e)}-z_{\rm head(e)})
&=\sum_{i>0} F_i\cdot(q_i-q_0)\\
&\ge \sum_{i>0}\{\mu_i(c_i-a_{ix})+d_{ix}-\|d_i\|\}.
\end{aligned}
\]
The equality is discrete summation by parts; the inequality follows
from the support and \(\|q_i\|=1\). If every rod length were at most \(U\),
the left side would instead be at most \(U\sum_e\|f_e\|\). For each
accepted leaf, the verifier proves the lower bound **strictly exceeds**
this upper bound using integer rounded-up Euclidean norms. An optional
SciPy LP finder proposes data but is never imported by exact replay.
These are newly generated native force certificates; the published
reference supplied the force-lemma idea, not the data or an executable.

## Complete partition and replay

| Owners | Canonical graphs | Energy | Septagon | Force | Force leaves | Closed splits |
|---:|---:|---:|---:|---:|---:|---:|
| 12 | 6,277 | 34 | 22 | 6,221 | 6,230 | 9 |
| 13 | 12,867 | 0 | 0 | 12,867 | 14,611 | 1,744 |
| 14 | 4,391 | 0 | 0 | 4,391 | 5,835 | 1,444 |
| Total | 23,535 | 34 | 22 | 23,479 | 26,676 | 3,197 |

The [candidate energy theorem](DISKCOVER_NATIVE_N19_CANDIDATE_GRAPH.md)
handles exactly verified subgraph membership, not a numerical proximity
test. The independent septagon stress certificates cover their 22
specified graphs; the verifier checks this family before permitting any
such routing. No empty leaf or unresolved graph is used.

After regenerating both native census traversals, run:

```sh
python verification/n19/replay_force_archive.py PATH_TO_CENSUS --workers 4
```

The directory must contain the canonical `dfs-{12,13,14}.json` and
`audit-{12,13,14}.json` outputs. Replay needs only the Python standard
library. It reads the three deterministic gzip JSONL bundles directly,
with no extraction. Each owner count, chunk boundary, graph index,
canonical face list and proof disposition is bound to the fresh census.
Missing, unsound, disordered or unresolved records cannot produce a
completed replay.

SHA-256 of the bundled compressed evidence:

```text
e8d69e0647f011ebc8213b06de9934b82a76f6e8c1736b7d952db27c38fc4f07  force-b12.jsonl.gz
bcc2caf240262bb8c245bac1d9f733591c242905d7a0cc5675742565ed710bef  force-b13.jsonl.gz
9b5f728c16e2c4fe17bb456e505ddff74b28fedfdff5a404dcf3f0e63253d92a  force-b14.jsonl.gz
```

Hashes identify the delivered bytes; they are not proof verdicts. The exact
comparison with the regenerated census and the mathematical replay are both
required.
