<!-- SPDX-License-Identifier: MIT -->
## Excluding eight boundary owners in the ten-disk problem

Use unit covering disks on a target of radius $R=1+2\cos(2\pi/9)$. A cover
at smaller radius would give strict unit-radius coverage on this target, and
we assume such a strict cover. Put $B=\arcsin(1/R)$, $A=\arcsin(2/R)$.
For elementary comparisons below use $2.532<R<2.533$,
$.40599<B<.40600$, $.9105<A<.9108$, and
$3.14159265<\pi<3.14159266$. The intervals and distance margins can be
checked by the directed intervals in [the replay](../tools/diskcover_n10_area.py).

Normalize all centers to norm less than $\sqrt{R^2-1}$, using first the map
$c\mapsto\lambda c$, $\lambda=(R^2-1)/\|c\|^2$, for larger norms:
$$
|x-\lambda c|^2-1=\lambda(|x-c|^2-1)+(1-\lambda)(|x|^2-R^2).
$$
Strict coverage persists, so a small generic perturbation puts all centers
strictly inside the bound and avoids three-way nearest ties on the boundary.
Each bisector chord on the target boundary then has length greater than 2.
An owner has one connected nearest arc: a competitor beating it strictly
between two owned points would cross that short footprint arc twice, both
crossings inside a unit disk and thus at distance at most 2. The arcs
partition the circumference. As $7B<\pi$, there are at least eight owners.
For exactly eight, denote their disks by $C_i$ and their arcs by
$q_i\to q_{i+1}$, with cyclic indices and successive angular gaps at most $2B$.

No three of these disks share a point: if they did, all their boundary
footprints would lie in the radius-2 disk centered at that point, hence
would have total union angle at most $2A$. The other five disks contribute
at most $10B$, and $A+5B<\pi$.

Follow the pair bisector inward from $q_i$ until the distance to both
centers first reaches 1, giving $p_i$ in the target interior. The distance
starts strictly below 1, and it reaches 1 before exit because the target
bisector chord is longer than 2. No third boundary disk contains $p_i$
by the preceding no-common-point result; the two incident disks contain
$p_i$ only on their boundaries. Thus one of the other two disks must
contain $p_i$, by strict coverage.

The polar angle of $p_i$ differs by at most $A$ from both anchors
$q_{i-1},q_{i+1}$, since each anchor is within distance 2 (they share an
incident covering disk with $p_i$); the tangent to the radius-2 disk
centered at an anchor gives that angular bound. The two comparisons use
the same angle lift because the anchors differ in the prescribed lift
by at most $4B$, with $4B+2A<2\pi$. For offset $j=3,4$, compare
$q_{i+1}$ with $q_{i+j-1}$ and sum intervening gaps to obtain forward
angular separation at most $2A+2(j-2)B$, and backwards at most
$2A+2(6-j)B$. Both bounds are less than $2\pi$, making the two
separations positive. For $j=3$ the short angle is at least
$\psi=2\pi-2A-6B$ (the forward angle is less than $\pi$); for $j=4$
it is at least $\xi=2\pi-2A-4B$. Both lower bounds exceed $\pi/2$.

**Radial estimate.** Let $\theta_i$ be the angular length of the union of
the two full footprints incident to $p_i$; they overlap at $q_i$,
so the union is one arc of length at most $4B<\pi$. The remaining six
footprints give $\theta_i\ge2\pi-12B$. Define
$$
 D(u)=R\cos u-\sqrt{1-R^2\sin^2 u},\qquad h(4u)=2D(u)\cos u-R.
$$
We show $|p_i|\ge h(\theta_i)$, without assuming symmetric disks.
Let $u_0=\theta_i/4>.3528,\ t_0=h(4u_0)>1$. For a footprint of
half-width $u$ whose center has norm $d$, the endpoint equation
gives $d\ge D(u)$. If a point of norm $t$ is in this disk, its polar
angle differs from the center's by at most
$\arccos((d^2+t^2-1)/(2dt))$. Here $t>0$ since $d\ge R-1>1$.
Assume $t<t_0$. We may replace $t<1$ by 1 in this constraint because
the allowance increases up to 1 when $d\ge R-1>\sqrt2$. Also
$t_0\le h(4B)=R-2/R$, so $d^2>t_0^2-1$; replacing $d$ by
$D(u)$ only relaxes the constraint to an allowance
$$
 \gamma_t(u)=\arccos\!\left(\frac{D(u)+(t^2-1)/D(u)}{2t}\right).
$$
For $t\ge1$, $D(u)$ is increasing and convex
($D'=R\sin u\,D/\sqrt{1-R^2\sin^2u}$); the argument is increasing and
convex as a function of $D$, and arccosine is decreasing and concave
on $[0,1]$. Hence $\gamma_t$ is concave on its feasible interval.

For the incident disks' half-widths $u_1,u_2$, write $w=(u_1+u_2)/2$.
The union length is at most $4w$, so $w\ge u_0$. Neither footprint can
contain the other, since the union length would then be at most $2B$,
contrary to $2B<2\pi-12B$. Each center angle has a common lift relative
to $p_i$ in $[-\pi/2,\pi/2]$; overlapping footprints cannot overlap only
via the alternative circular lift since $2B<\pi$. Thus their union length
is at most the sum of their half-widths and center angular separation:
$$
 4u_0\le 2w+\gamma_t(u_1)+\gamma_t(u_2)\le 2(w+\gamma_t(w)).
$$
For $d_0=D(u_0)$, the unit circles with centers of norm $d_0$ at
angles $\pm u_0$ both meet the radial boundary point at $R$. Their
other radial intersection is its reflection across $d_0\cos u_0$,
namely $t_0$. Hence $\gamma_{t_0}(u_0)=u_0$ and
$d_0^2-1-t_0^2=2t_0(d_0\cos u_0-t_0)\ge0$.
Since $D(w)\ge d_0$, the allowance at $w$ strictly increases from
$t$ to $t_0$, by differentiation in the radial argument. At $u_0<B$,
with $z=\sqrt{1-R^2\sin^2u_0}$, the derivative satisfies
$$
 -\gamma_{t_0}'(u_0)=\frac{R(d_0-t_0\cos u_0)}{t_0 z}
 \ge\frac{2R^2\cos u_0\sin^2u_0}{t_0 z}>1.
$$
The inequality uses $d_0-t_0\cos u_0=R\cos u_0-d_0\cos(2u_0)$
and $d_0\le R\cos u_0$. For strictness use $R>2.53$,
$\sin u_0>.34,\cos u_0>.91,z<.52,t_0\le R$, giving the rational
bound $2(2.53)(.91)(.34)^2/.52>1$.
Concavity consequently gives $w+\gamma_{t_0}(w)\le 2u_0$, contradicting
the upper bound with $t<t_0$. For $u_0=B$, necessarily $w=B$ and
$\gamma_{t_0}(B)=B$ gives the contradiction directly.

For the monotonicity and convexity used above, differentiating $h(4u)$
gives $2\sin u\,D(u)^2/\sqrt{1-R^2\sin^2u}$. All its factors are
nonnegative and increasing, giving the claims by continuity through $B$.
In particular $t_0\ge h(4\cdot .3528)>1$ by direct outward evaluation.

The pairs of disks incident to $p_i,p_{i+j}$ are disjoint; the four
other disks cover angle at most $8B$, so
$\theta_i+\theta_{i+j}\ge2\pi-8B$. Jensen and the radial estimate give
radial sum at least $2h(\pi-4B)$. The distance at short angle $\alpha$
and radii $x,y$ is at least $(x+y)\sin(\alpha/2)$: on squaring, the
difference is $(x-y)^2\cos^2(\alpha/2)$. The resulting lower bounds
$2h(\pi-4B)\sin(\psi/2)$ and $2h(\pi-4B)\sin(\xi/2)$ both exceed 2.
Indeed $(\pi-4B)/4>.37939816$, and $h(\pi-4B)>1.191$
by substituting $u=.37939816$, $R=2.532$ in $h(4u)$;
$h(4u)$ increases in $R$ for fixed $0<u\le B$, directly from
$h(4u)=R\cos(2u)-2\cos u\sqrt{1-R^2\sin^2u}$. Using the upper
bounds for $A,B$ above gives $\sin(\psi/2)>.848$ and
$\sin(\xi/2)>.988$, by monotonicity and the alternating Taylor lower
bound through degree 7 at the corresponding lower angle endpoints.
The rational products $2(1.191)(.848)$ and $2(1.191)(.988)$ exceed 2.
Thus offset-3 pairs form an eight-cycle requiring alternating assignment
to the two remaining disks, but any offset-4 pair then has the same
assignment while also lying farther than 2 apart. This is impossible.
