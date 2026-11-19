<!-- SPDX-License-Identifier: MIT -->
# n=19: native twelve- and thirteen-owner branch reductions

These are strict-cover **necessary conditions**, not complete branch
exclusions. No external $n=19$ result is used; the candidate radius
$U=1/\sqrt{13}$ is independently checked as an upper bound in
[the n19 replay](../tools/diskcover_n19_upper.py).

## Normalization and scope

Suppose a smaller-radius cover of the unit disk exists. It gives a
uniform strict margin at $U$. Apply the radial normalization and
generic perturbation of
[the native n10 clipped Voronoi argument](DISKCOVER_N10_OUTER_JUNCTIONS.md),
now scaled to the unit target and radius $U$. The normalized strict
cover has distinct centers of norms $<\sqrt{1-U^2}$ and no nongeneric
Voronoi incidences. An owner is a center with a positive-length
boundary arc in the clipped Voronoi diagram, not just a disk touching
the boundary. Each owner has one arc, because otherwise a competitor
bisector would cross the same unit boundary footprint twice, with a
chord at most $2U$, but every bisector cuts a chord longer than $2U$.
The clipped dual is a triangulated topological disk with owner sites
forming its boundary cycle. All its edges join sites of distance
at most $2U$, by an incident point of the clipped Voronoi cells.

There are at least 12 owners by boundary angular capacity, and
there cannot be 15 or more: each owner site has norm $>1-U$, so a
concentric core disk of radius $1-2U$ would be covered by at most
four nonowner disks. Four equal disks covering that core require
$U\ge (1-2U)/\sqrt2$ by the boundary arc bound, a contradiction
to $(2+\sqrt2)^2<13$. Thus owner counts 12, 13, and 14 exhaust
the normalized strict-cover problem. The distinct footprint count
is discussed in [the main n19 note](DISKCOVER_NATIVE_N19.md).

## Owner chords

Write $a=\arcsin U$ and $b=\arcsin(2U)$; each owner arc has
half-angle at most $a$. For any edge between two owners, choose
the shorter span in number of owner slots from one end-owner
through the other, with $k$ owner arcs including both ends.
Let its starting and ending switches be $p,q$ on the unit circle.
The two end-owners have center distance at most $2U$;
since $p,q$ are within $U$ of the respective sites,
$|p-q|\le4U$. The angle of the span is at most $2ka$.
For $B=12,13$, we have $k\le7$, and the inequalities below give
$14a<2\pi-2b$. Hence the span with chord at most $4U$
cannot have the major angular value and has angle at most $2b$.
The complementary $B-k$ owner arcs therefore imply
\[
 \pi \le b+(B-k)a.
\]
Since $b+9a<\pi$, this proves:

* **12 owners:** all edges joining two owners are boundary-cycle
  edges. In particular every boundary edge is incident to a
  triangle whose third vertex is a nonowner.
* **13 owners:** any nonboundary edge joining owners can connect
  only owners at cycle distance two. The small side of such a chord
  has three boundary vertices, but it might contain some of the
  six nonowner sites: it is not necessarily an ear. Two chords with
  interleaved endpoints are impossible by planarity.

## Nonowner degree into the boundary cycle

Fix a nonowner site $c$ incident to $k$ owners. The ownership arc of
every such owner is in the disk of radius $3U$ about $c$: each of its
points is within $U$ of the corresponding owner site, and that site
is within $2U$ of $c$. Thus those $k$ owners jointly account for
at most $2\arcsin(3U)$ of boundary angle, independent of how their
arcs are ordered. Consequently
\[
 \pi \le \arcsin(3U)+(B-k)a .
\]
Since $\arcsin(3U)<1$ and $1+7a<\pi$, a nonowner can be
adjacent to at most four owners when $B=12$, or five when $B=13$.

If $c$ covers the origin, $\|c\|\le U$. A radius-$3U$ disk whose center
has norm $d\le U$ has unit-boundary half-width at most
$\arccos(5/(2\sqrt{13}))<.81$. In fact for $d>0$ the cosine at
a boundary intersection is $(d+(1-9U^2)/d)/2$; it decreases to
$d=U$ on this interval, because $U^2<1-9U^2$. A disk not meeting
the circle contributes no angle. Since $.81+8a<\pi$ the origin
site has at most three owner neighbors when $B=12$, or four
when $B=13$. If moreover $\|c\|\le1-3U$, then it has no such
neighbors, as each owner has norm $>1-U$.

## Closed subcase for twelve owners

For each of the 12 boundary-cycle edges, assign the nonowner
vertex in its unique incident triangle. **At least five different
nonowner vertices are needed.** A site with at most four owner
neighbors can take at most three assignments: the graph induced
by four vertices of the 12-cycle is a forest of paths. If four or
fewer sites sufficed, then exactly four would be used, each having
three edges assigned on four consecutive owners. The four
three-edge paths would partition the cycle; their four transition
owners would be counted twice in the sum of path arc lengths.
Their total half-width is at least $\pi-8a$ by the cap on
the other eight owners. Thus the four radius-$3U$ disks about
the four nonowners would need combined half-width at least
\[
 2\pi-8a>4,
\]
whereas each has half-width at most $\arcsin(3U)<1$. This is a
contradiction. At most two of the seven nonowners can therefore
be absent from the boundary-edge assignments. This does not
exclude the five-, six-, or seven-site assignments.

## Exact scalar check

The only transcendental lower input here is $\pi>3.14159$.
All other scalar comparisons follow from the alternating Taylor
bounds for sine and cosine on $[0,1]$ and rational arithmetic.

```python
from fractions import Fraction as F

pi_lo = F("3.14159")
a_hi, b_hi = F(".2811"), F(".589")
sin_lo = lambda x: x-x**3/6
assert sin_lo(a_hi)**2 > F(1, 13)
assert sin_lo(b_hi)**2 > F(4, 13)
assert sin_lo(F(1))**2 > F(9, 13)
assert 14*a_hi + 2*b_hi < 2*pi_lo
assert b_hi + 9*a_hi < pi_lo
assert 1 + 7*a_hi < pi_lo
assert (1-F(".81")**2/2+F(".81")**4/24)**2 < F(25,52)
assert F(".81") + 8*a_hi < pi_lo
assert 2*pi_lo - 8*a_hi > 4
```

## Twelve-owner transition pruning

Label each boundary edge by its assigned core vertex. Let $q$ be the
number of distinct labels and $m$ the number of transition owners:
the owners whose two incident boundary edges have different labels.
For each label the owner-endpoint set of its assigned edges is
contained in its radius-$3U$ footprint, as above. The combined
half-width budget of the $q$ footprints is at least
$\pi+\sum_{\mathrm{transition}}t_i\ge 2\pi-(12-m)a$:
every owner is counted once, and the $m$ transition owners are each
counted once more. Here $t_i$ denotes an owner half-angle. Therefore:

* If $q=5$, then $m\le7$ since $2\pi-4a>5$.
* If $q=5$ and an origin-covering site is an assignee, then $m\le6$
  since the sum of the five footprint caps is below $4+.81$,
  and $2\pi-5a>4+.81$.
* If $q=6$, then $m\le10$ since $2\pi-a>6$.

Every assignee with $e$ assigned edges occurring in $j$ separate
cyclic runs is adjacent to at least $e+j$ outer sites, the distinct
ends of its runs. Thus $e+j\le4$, or $e+j\le3$ for an origin
site. In particular three edges must be consecutive, and only
a two-edge assignment can occupy two separate runs. For $q=5$,
the only positive edge-count multisets summing to 12 with each
count at most 3 are $(3,3,2,2,2)$ and $(3,3,3,2,1)$.
In the former, at least one two-edge label must be consecutive,
and if the origin site participates at least two must be consecutive.
In the latter, at most one label can ever be split, independently
of the global transition budgets. These cuts are filters on
the as-yet unpaid remaining annulus assignments.

```python
from fractions import Fraction as F

pi_lo, a_hi = F("3.14159"), F(".2811")
assert 2*pi_lo - 4*a_hi > 5
assert 2*pi_lo - 5*a_hi > 4 + F(".81")
assert 2*pi_lo - a_hi > 6
```

## Thirteen-owner diagonal multiplicities

For $B=13$, associate with each outer chord its short span of three
owners. Spans with starting positions one apart would give interleaving
chords and are forbidden. Spans overlap only at a shared endpoint,
and each owner belongs to at most two spans. The intersection graph
of the selected spans is a union of paths: edges between starts at
distance two are edges of the 13-cycle in step-two order, and not
all starts can be selected since neighboring starts in step-one
order interleave. If there were at least five spans, this path
graph would have an independent set of at least three spans.
Their nine disjoint owners use half-width at most $3b$, and the
other four use at most $4a$, contrary to $3b+4a<\pi$. Therefore
there are at most four outer chords. This argument does not treat
small-side core sites as absent.

If there are four chords, write the angular deficit of owner $i$
as $d_i=a-t_i\ge0$. Its total is $13a-\pi$. Each span contributes
at least $3a-b$ in deficits, and multiplicities are at most two.
Hence the total deficits over owners appearing **at most once**
in the spans are at most
\[
 2(13a-\pi)-4(3a-b)=14a+4b-2\pi < .005.
\]
Indeed, twice the overall deficit less the sum over the four
spans charges every such owner at least once. In particular
their half-angles are greater than $a-.005$. No span can be
isolated from the other three: it would need deficit at least
$3a-b>.005$ from such owners. The four spans thus form either a
four-vertex path or two two-vertex paths. These are necessary
restrictions, not exclusions of both remaining patterns.

```python
from fractions import Fraction as F

pi_lo = F("3.14159")
a_hi, b_hi = F(".2811"), F(".5881")
sin_lo = lambda x: x-x**3/6+x**5/120-x**7/5040
assert sin_lo(b_hi)**2 > F(4, 13)
assert 3*b_hi + 4*a_hi < pi_lo
assert 14*a_hi + 4*b_hi - 2*pi_lo < F(".005")
assert 3*F(".277")-b_hi > F(".005")  # a > U > .277
assert F(".277")**2 < F(1, 13)
```
