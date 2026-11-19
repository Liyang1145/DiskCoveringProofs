<!-- SPDX-License-Identifier: MIT -->
# Ten disks: exact global optimum and replay

**Status:** the exact covering radius is proved below by an attaining
construction and a lower argument for arbitrary centers. The geometry is
a written proof, and the strict numerical inequalities are checked by
directed rational arithmetic. It is not a Lean formalization.

Gábor Fejes Tóth, [*Thinnest Covering of a Circle by Eight, Nine, or Ten
Congruent Circles*](https://library.slmath.org/books/Book52/files/18fejes.pdf),
*Combinatorial and Computational Geometry*, MSRI Publications 52 (2005),
pp. 361–376, states the theorem in §1, proves the common geometric reduction
and area argument in §2, and gives the remaining ten-disk argument in §3.
The cited paper uses unit covering disks and a variable target radius. Scaling
back to this repository's unit target gives
$$U=r_D(10)=\frac{1}{1+2\cos(2\pi/9)}.$$

## Direct exact upper bound

Let $d=\pi/9$, $c=\cos d$, $r=(4c^2-1)^{-1}$, and
$a=2rc$. Place one center at the origin and the other nine at distance
$a$ on the rays of angles $2k\pi/9$. The origin disk covers all points
at distance at most $r$. For any other point, take its nearest ray,
let $s\in[r,1]$ be its distance from the origin and
$|\theta|\le d$ its angular distance from the ray. Its squared distance
to the associated center is at most $s^2-2sac+a^2$. At $s=r$ this
expression is $r^2$, since $a=2rc$; at $s=1$ it is also $r^2$, since
$1-4rc^2+4r^2c^2-r^2=(1-r)(1-r(4c^2-1))=0$.
Convexity in $s$ gives the required bound on the entire interval.

## Exhaustive lower bound

At target radius $R=1/U$ in unit covering-disk units, fewer than eight
boundary owners have insufficient angular capacity. The origin-covering
disk cannot reach that circumference ($R>2$), leaving at most nine
boundary owners. Strict coverage permits the radial normalization and
general-position perturbation given in the first note below. The three
remaining cases are:

1. [Eight owners](DISKCOVER_N10_EIGHT_OWNERS.md): the inward meeting
   points for owner pairs cannot be covered by the other two disks.
   The radial bound is proved without a symmetry assumption; the
   pair-arc budget uses the correct inequality direction.
2. [Nine owners with an outer triple](DISKCOVER_N10_OUTER_JUNCTIONS.md):
   the clipped Voronoi dual has one ear or two ears sharing an endpoint.
   The exact fan-area comparisons contradict the target disk's area.
   The corrected chord-angle bound and area sums do not use the
   paper's printed decimals as proof inputs.
3. Nine owners and no outer triple: the native perimeter argument below
   rules out this branch directly. No classification of equality is
   needed to exclude a strictly smaller covering radius.

Run `python tools/solve_diskcover.py 10 --require-global-proof` to return
the exact radius, ten centers, the proof references, and fresh checks.
The directed script is `python tools/diskcover_n10_area.py`.

## Native replay of the nine-owner, no-outer-triple case

Let $U=1/(1+2\cos(2\pi/9))$. Assume a strictly smaller radius works,
so the cover has a positive uniform distance margin at radius $U$.
Use the same radial normalization and general-position perturbation as
[the native eight- and nine-disk replay](../tools/diskcover_global.py):
each center has norm less than $\sqrt{1-U^2}$, the covering remains strict,
and there are no four cocircular centers or triple boundary ties.
Each pair bisector then cuts a unit-circle chord longer than $2U$.
Consequently the positive-length nearest-center ownership arcs are
connected: a reentry inside one disk's short boundary arc would give
two intersections with one competitor bisector inside the disk,
contradicting the chord length.

Suppose there are exactly nine such owners, $c_i$ in cyclic order, and
no clipped Voronoi vertex shared by three owners. The remaining center
$z$ covers the origin, since a radius-$U$ disk containing the origin
cannot touch the boundary ($2U<1$). The full Voronoi cell of $z$ is
strictly inside the open unit disk: it contains $z$, is convex, and
has no point on the unit circle. At every transition between $c_i$
and $c_{i+1}$ the Voronoi edge must end at an interior vertex (another
endpoint on the unit circle would contradict the chord bound). Its
third center is $z$. These vertices give all nine consecutive pairs of
facets on the bounded cell of $z$: each of its facets is an intersection
with a single owner bisector, and every owner appears in the cyclic
chain. Thus the positive angles $\gamma_i$ between successive outward
normals $c_i-z$ sum to $2\pi$ and lie in $(0,\pi)$. The circumradius of
the triangle $(z,c_i,c_{i+1})$ equals the nearest-center distance at
the corresponding vertex and is strictly less than $U$. The sine rule
and Jensen give the strict upper bound on the cyclic walk length $P$:
$$P<18U\sin(2\pi/9).$$

For the converse, project the walk onto a unit vector $v$. The total
variation is at least twice its width, $2(H(v)+H(-v))$, where
$H(v)=\max_i c_i\cdot v$. Integrating over a half-turn gives
$P\ge\int_{S^1}H(v)\,dv$. Write $t_i$ for the ownership half-angles.
Averaging the squared distances to the endpoints of the $i$-th arc and
dropping the nonnegative squared lateral coordinate gives
$c_i\cdot v_i\ge\cos t_i-\sqrt{U^2-\sin^2 t_i}$ along its midpoint
direction $v_i$. Integration over that arc yields a lower contribution
$2(t_i-G(t_i))$, where
$G(t)=t-\sin t\cos t+\sin t\sqrt{U^2-\sin^2 t}$. Write $s=\sin t$, $c=\cos t$, and $h=\sqrt{U^2-s^2}$. On the interior,
$$h^3G''(t)/s=4ch^3-U^4-3U^2+6U^2s^2+2s^2-4s^4.$$
Use $ch^3\le U(U^2-s^2)$ and drop the last term. The resulting
affine function of $s^2$ increases, since $2-4U+6U^2>0$. At
$s^2=U^2$ it is $U^2(5U^2-1)<0$. Thus $G$ is concave by continuity
on $[0,\arcsin U]$.
Here $U<2/5$ follows from $2\pi/9<7/10$ and
$\cos(2\pi/9)\ge 1-(2\pi/9)^2/2>3/4$. Since $\sum_i t_i=\pi$,
Jensen gives, with $d=\pi/9$,
$$P\ge18\sin d\left(\cos d-\sqrt{U^2-\sin^2 d}\right)
       =18U\sin(2d).$$
The equality uses the smaller root $2U\cos d$ of
$a^2-2a\cos d+1=U^2$. This contradicts the strict upper bound.
It rules out this branch without a separate equality classification
or the printed area estimates.
