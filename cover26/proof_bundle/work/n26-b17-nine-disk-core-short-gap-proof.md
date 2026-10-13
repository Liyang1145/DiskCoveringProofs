# A NEW necessary short ownership gap in the entire B=17 family

This is a geometric necessary condition, not a complete n=26 lower bound,
enumeration acceptance or optimality claim. It does not assume the candidate's
D2 symmetry, stationarity or a particular triangulation.

Use the current cyclic boundary-ownership reduction of an irreducible cover
of the closed unit disk D by at most 26 equal disks of radius rho<=U, with
U=234701/1000000. Suppose there are exactly B=17 boundary owners.
The owners have contiguous cyclic arcs; their endpoints are in their own
closed disks. The existing unit-cap/no-return ingredient gives each ownership
arc length less than a half turn. B means owners, NOT all disks touching D.
There are at most nine nonowner disks. Abstractly starred labels do not create
additional physical disks or alter this counting argument.

## Explicit external radius theorem, not a new proof of it

Gabor Fejes Toth, “Thinnest Covering of a Circle by Eight, Nine, or Ten
Congruent Circles”, MSRI Publications52 (2005),361–376, theorem on p362,
states R_n=1+2*cos(2*pi/(n-1)) for n=8,9,10, where R_n is the largest target
disk radius covered by n unit disks. Its n=9 radius clause therefore gives
the necessary small-disk radius lambda9=sqrt(2)-1 for covering a unit disk
with at most nine congruent disks. The at-most statement follows by adding
extra disks if needed. Only the radius clause is imported; no coordinate or
uniqueness clause is used, matching the earlier eight-disk import policy.

Official primary publication:
`https://library.slmath.org/books/Book52/files/18fejes.pdf`.
The official publication's theorem text was inspected. The already registered
local PDF was freshly rehashed:
`29ca1999cc706747658082c0e459da78fda62ec356d6277a4f16b4878bd16917`.
Local fitz/pypdf are unavailable, and fresh screenshot-tool calls failed;
this note does not claim a fresh local text extraction or image verification.
The existing source review had independently checked the page images.
The external theorem is explicitly relied on, not re-proved by hashes or code.

Use the weaker rational lambda=207/500=.414. It is STRICTLY below lambda9:
2-(1+lambda)^2=151/250000>0.

## Core coverage forces an inward boundary owner

Let c be the minimum norm of any boundary-owner center. Every owner meets the
unit circle, so 1-rho<=c<=1+rho. Thus 0<c-rho<=1, since rho<=U<1/2;
the core below is contained in D.
No boundary-owner disk covers a point of the open core |x|<c-rho.
The at most nine nonowner disks cover that open core; their finite closed
union therefore covers its closure. Similarity scaling and the external
nine-disk theorem give

rho >= lambda9*(c-rho) >= lambda*(c-rho).

Consequently at least one owner center p has
|p|<=rho*(1+1/lambda)<=K,
where K=165933607/207000000.

## That owner must have an ownership gap below 9/200 turns

Set a=9/200 turns. Suppose this owner's endpoint gap is s>=a.
For its endpoints A,B on the unit circle, use their mid-angle unit vector v.
Since the ownership arc is less than half a turn, cos(pi*s)>=0, and

(|A-p|²+|B-p|²)/2
=1+|p|²-2*(p.v)*cos(pi*s)
>=1+|p|²-2*|p|*cos(pi*s).

Cosine monotonicity on the relevant interval and an outward upper bound C on
cos(pi*a) yield a lower bound 1+t²-2*t*C, with 0<=t=|p|<=K.
Since K<C, this expression decreases on [0,K]. Hence the mean endpoint
distance squared is at least 1+K²-2*K*C.

The exact trigonometric arithmetic gives

1+K²-2*K*C-U²
=573513929845138326460849663169091956002765980386967664026694942247
/2142450000000000000000000000000000000000000000000000000000000000000000
>0.

At least one endpoint would therefore have distance greater than U>=rho,
contradicting its membership in the owner's closed disk.
Thus at least one of the seventeen cyclic ownership gaps is STRICTLY
less than 9/200 turns, i.e.16.2 degrees.

The arithmetic checker also proves the same strict inequality with an
independent, weaker rational cosine upper bound:
pi>314159/100000 and cos(x)<=1-x²/2+x⁴/24 on the small positive interval.
These are whole-domain inequalities, not numerical samples.

## Safe future use

For each actual B17 source state, true covers lie in the UNION of seventeen
closed angular subdomains s_i<=9/200. All seventeen cases must be retained
and proved or excluded; overlaps must not be counted as disjoint payments.
The closed <= relaxation safely includes all true strictly-short gaps.
No source node is removed merely because a rod-model sample violates this.
Do not apply this B17/I<=9 argument to B16/I=10 or other families.

The numerical U is the CURRENT conservative screen bound. The result also
applies to rho<=Rstar<U, but it does not relabel any inherited original-U
queue or already sealed executor. Frozen source code, paid leaves, newest
histories and original-U accounting are unchanged. Complete source binding,
independent rechecking of any actual state exclusion, all lower
classifications and the final unrestricted joint gate remain required.
