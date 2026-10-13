# Projection, closed-cap domination and the no-return bridge

This supplies universal algebraic identities and an explicit ordered-real
argument for two continuous geometric ingredients. It is not the final
unrestricted reduction/joint acceptance, a complete catalogue, a new payment,
or a proof-assistant formalization. Frozen geometry flags remain unchanged.

## Projection

For a centre c=u*v with u>=1 and |v|=1, and p in the closed unit disk, set
z=v.p<=1. Projection c'=v satisfies

|p-c|^2-|p-c'|^2=(u-1)(u+1-2z)
                 =(u-1)^2+2(u-1)(1-z)>=0.

The two identities are checked as exact polynomials, not at sampled centres.
Thus projecting an outside centre onto the closed disk cannot lose coverage.
The slack/generic-position perturbation and subsequent irredundant-subcover
arguments remain separate steps of the complete interface.

## Universal closed-cap domination

Work in orthonormal coordinates. Let 0<=r2<1, 0<t<=1, s>=0,
t^2+s^2=1. Put q+=(t,s), q-=(t,-s) and c=(a,b).
Assume BOTH |q+-c|^2<=r2 and |q--c|^2<=r2. Then every p=(x,y) with
x^2+y^2<=1 and x>=t satisfies |p-c|^2<=r2.

Write delta+ = r2-|q+-c|^2, delta- = r2-|q--c|^2 and
deltaD=1-x^2-y^2. The exact identities give

2*t*a=(1-r2)+a^2+b^2+(delta++delta-)/2>0.

As t>0, this proves a>0. Also

s^2-y^2=deltaD+(x-t)(x+t)>=0.

Here x+t>0 and s>=0, hence -s<=y<=s. For b>=0:

r2-|p-c|^2=delta-+deltaD+2*a*(x-t)+2*b*(s+y)>=0.

For b<=0:

r2-|p-c|^2=delta++deltaD+2*a*(x-t)-2*b*(s-y)>=0.

The two sign cases exhaust every real b. All equalities are exact modulo
t^2+s^2-1=0, with every summand's sign explicitly justified. Closed endpoints,
zero endpoint slacks, b=0, s=0 and x=t are included. This is a universal
ordered-real proof, not an inference from finite regression examples.

## Squared-distance/private-point implication

For two distinct centres choose the normal along their difference, so
c_i=(a,b), c_j=(a+d,b), d>0. Their bisector is x=t=a+d/2, and

|p-c_i|^2-|p-c_j|^2=2*d*(x-t).

Thus a private point of disk j, with |p-c_j|<=rho<|p-c_i|, must lie in
the open cap x>t. If both cap endpoints lie in disk i and rho^2<1, the
closed-cap domination lemma places the ENTIRE unit-disk cap in disk i.
No such private point exists, so disk j is redundant. The polynomial
distance identity is checked separately modulo 2*t-2*a-d=0.

## No-return bridge for an irredundant equal-disk cover

Let closed equal disks of radius rho<1 cover the closed unit disk and be
irredundant. Each disk has a point not covered by any other closed disk.
Every point of a clipped nearest-centre Voronoi cell is covered by its owner.
If centre c_i meets the unit circle, its disk-circle footprint is a single
short arc: its angular condition has positive threshold
(1+|c_i|^2-rho^2)/(2*|c_i|)>0. A zero centre has no boundary footprint
when rho<1. Empty/tangent footprints cannot supply a returning boundary arc.

Suppose the cell's boundary ownership returns within that short footprint.
Choose two owned circle points P,Q in different components and a non-owned
point between them on the short footprint. Some other centre j is strictly
closer at that point. Its winning set on the unit circle is a single open
half-plane cap. Since P,Q are outside this cap, the cap lies between them
within the short footprint, so its length is less than pi and its threshold
t is positive. Both cap endpoints are covered by disk i.

Closed-cap domination and the private-point implication above make disk j
redundant, a contradiction. Therefore boundary ownership does not return.
General-position assumptions can remove endpoint multiple-tie degeneracies
using the separately justified strict-radius slack; they are not inferred
from numeric samples or from the candidate's symmetry.

## Circle-footprint half-angle bound

For a nonzero centre of norm v>0, the circle-footprint threshold is
h=(1+v^2-rho^2)/(2*v)>0 when rho<1. An additional exact identity gives

4*v^2*(h^2-(1-rho^2))=(v^2-(1-rho^2))^2>=0.

Thus h>=sqrt(1-rho^2). If the footprint is nonempty, its half-angle is at
most arcsin(rho). Empty/tangent footprints give no larger arc. This supports
the boundary-counting ingredient but does not replace the actual n-specific
strict trigonometric threshold, externalN8 theorem or complete joint gate.

## Scope of the checker

The companion checker verifies eight polynomial identities, their exact
equality owners, stated hypotheses and both sign decompositions. The
ordered-real implications and circle-arc/private-point bridge are written
explicitly here; a code/hash/green check alone does not certify the entire
continuous reduction. No native/source acceptance flag or proof level is
promoted. The complete simple triangular-disk dual, m<26 abstract starring,
four-family counting with the actual externalN8 theorem, origin pruning,
complete enumeration and lower classification, actual byte binding and final
joint acceptance are still required before n26 global optimality.
