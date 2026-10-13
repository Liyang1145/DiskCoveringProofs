# Exact isolated-switch constraint from simultaneous inwardness

Fix actual allowance r in (0,1), unit P, and distinct centers c,d with |c|,|d|<=sqrt(1-r²) and |P-c|=|P-d|=rho in (0,r]. Let 2b in (0,pi) be the angle between c-P and d-P. Then
 **2 rho cos b >= r²+rho².**

Proof: write c=P+rho e1,d=P+rho e2 with unit e1,e2. Inwardness is equivalent to (-P) dot ej >= (r²+rho²)/(2rho)=A>0. Both ej therefore lie in the cone of half-angle arccos A about -P, so their angular separation2b<=2arccos A. Conversely if cos b>=A, choose ej to be rotations of -P by +/-b. Both centers then have norm²=1+rho²-2rho cosb<=1-r². Thus the criterion is necessary and sufficient for an isolated pair (not for a global nearest diagram). Equality forces both center norms to equal sqrt(1-r²) and the bisector to be -P.

In fixed R0=19/50 units put t=rho/R0, tau=75/76, and actual r in[3/8,U]. Necessarily
 **cos b >= R0*(t²+max(tau²,t²))/(2t).**
Indeed r>=max(3/8,rho). This is an exact isolated-pair feasibility criterion after existentially eliminating r in[max(3/8,rho),R0]; for actual r<=U it is a safe relaxation. Radius and angle are no longer independent. It implies t>= (1-sqrt(1-(3/8)²))/R0 >19/100, and b<pi/2. No lower bound from distinct-center separation is needed here.

A useful polynomial form is
 **2t cosb >= R0*(t²+max(tau²,t²)).**
For fixed b, put c=cosb and use actual r>=3/8:
 R0 t² -2ct +R0 tau²<=0,
 plus R0 t<=c (from actual r>=rho), t<=1.
If c²<R0²tau² the fiber is empty. Otherwise
 t in [(c-sqrt(c²-R0²tau²))/R0,(c+sqrt(c²-R0²tau²))/R0] intersect (0,min(1,c/R0)].
These intervals describe the normalized necessary relaxation exactly. The dual switch objective is a quadratic in t plus a linear angle term, so its maximum along this interval occurs at an endpoint or at its concave quadratic stationary point. This removes the radius parameter from switch maximization without relaxing the new constraint.

This differs from the old C840 midpoint inequality: the old argument bounded |(c+d)/2| only; here both individual center norms restrict the opening directions. It also differs from the prior triplet test, which matched a common radius but retained independent unrestricted switch angles.

Corollary: (r²+rho²)/(2rho)−r=(r−rho)²/(2rho)>=0, so cosb>=r. Equality in this corollary requires both rho=r and the symmetric cone-boundary pair. At rho=1−sqrt(1−r²) the cone has halfangle0 and the only pair is c=d; this is valid for isolatedpairs but excluded by distinctcenters inactualcovers.
