# Boundary switch geometry: positive exterior offsets and exact site-angle identity

Scope: inward-root 9+2 covering of unit disk, r<=19/50, essential neighbor-only actual arcs and rebuilt connected nearest-owned arcs, with the embedded refined straight-site Delaunay disk. No generic-position assumption. This fills the geometric sign detail used in COMPATIBLE-EDGE-SUPPORT and SHARED-FACTOR-DUAL, not a new global optimality assertion.

## 1. The boundary switch is on the exterior side of its straight dual edge
Let c,d be adjacent ring sites; m=(c+d)/2, a=|c-d|/2>0. Since |c|,|d|<1, m is strictly inside D. Their bisector has two exits from D. At the owned switch U choose unit n along mU, so U=m+ell*n, ell>0. The actual Voronoi edge enters D at U and ends at a finite common vertex z=m+t*n with t<ell. A refined triangle incident to the boundary edge has third site k at this z (for a cocircular polygon take the triangle adjacent to this edge). Write k=m+p*e+q*n, e parallel cd. Noncollinearity implies q!=0. Equidistance at z gives
  p²+q²-a² = 2tq.
Nearest-site validity at U gives
  |U-k|²-|U-c|² = p²+q²-a²-2ell*q = 2(t-ell)q >=0.
As t<ell, q<0. Thus k is on the side opposite U: n is genuinely exterior to the straight-site triangular disk at cd. This argument supplies the orientation; m in D alone supplies ell>0 but would not identify which side contains the faces.
If the Voronoi vertex is cocircular, every other incident site satisfies the same calculation; triangulation does not change the conclusion. The entering boundary edge has positive length by strict separation from other sites at the switch.

## 2. The switch angle is acute at either site
Let sigma=|U-c|=|U-d|. In triangle cUd the signed exterior base angle gamma is positive and tan(gamma)=ell/a. Put b=atan2(a,ell). Then 0<b<pi/2, gamma=pi/2-b, and sigma²=a²+ell². No signed-angle convention is needed to force this sign: it follows from section1. The older larger signed domain is a valid relaxation, not a contrary geometric premise.

## 3. Owned arc angle and ray order
For each inward-root ring site c, |c|²<=1-r² and c!=0. Every point W of its actual covered unit-circle arc satisfies
  c.(W-c) >= (1-|c|²-r²)/2 >=0.
Thus all site-to-owned-arc rays lie in the closed outward half-plane. As W traverses the unit circle, its polar angle about c increases strictly: its derivative has numerator 1-c.W>0 because |c|<1. The owned arc therefore sweeps a single angle alpha in [0,pi], not a major angle mistakenly inferred only from endpoints.
The refined straight triangles tile the inner polygonal star at c; their angles sum to its interior angle iota. The two boundary-edge exterior triangles have positive base angles gamma_left,gamma_right and disjoint interiors from the inner star by section1. The remaining rays are precisely the owned-arc sector, as follows alternatively by partitioning the convex clipped Voronoi cell into triangles from c: each edge contributes its site-to-endpoint angle, and its sole boundary arc contributes alpha. Internal bisector endpoint angles cancel telescopically, leaving iota+gamma_left+gamma_right+alpha=2pi. Hence
  alpha + sum_faces A_fc - b_left - b_right = pi.
An explicit algebraic version avoids any implicit ray-order assumption. For every incident primal straight edge its site wedge angle is theta_e=pi-a_e-b_e, including theta=0 for an artificial edge. If the ring vertex has dual degree d, exactly d-1 refined triangles meet it. Their angles not at this site sum to (d-1)pi-iota. Thus summing all incident wedges yields d*pi-((d-1)pi-iota)-b_left-b_right=pi+iota-b_left-b_right. The convex cell partition gives sum(theta_e)+alpha=2pi, proving the displayed identity directly. For a hub there are d triangles and the same counting gives its usual 2pi angle sum.

Here is the explicit wedge calculation, including obtuse angles. Put the current site at (0,0) and its neighbor at (2s,0), s>0. The primal edge is on x=s; orient its lower and upper endpoints as (s,-s*cot A) and (s,s*cot B), where A,B in(0,pi) are the opposite angles in the two incident Delaunay triangles. Since atan(cot A)=pi/2-A on this entire domain, its angle at the site is atan(cot B)-atan(-cot A)=pi-A-B. The genuine edge's endpoint order implies A+B<pi. For a cocircular artificial diagonal the endpoints coincide: A+B=pi and the wedge is zero; THE DUAL SITE DISTANCE 2s IS STILL POSITIVE. For a boundary edge one endpoint is the switch, with positive offset s*cot b, and the same calculation gives pi-A-b. In summing these formulas, each incident triangle contributes its two angles not at the current site exactly once, at its two incident edges. Artificial edges therefore cause no missing term and no generic perturbation is needed.

This is the bearing site-angle identity, with gamma located AT THE SITE. The switch apex is 2b. It is not an additional hypothesis H.

## 4. Exact area accounting
The clipped cells partition D. Each site belongs to its own cell and lies in D. For a ring's owned arc of width w<=2asin r, the arc chord has inward half-plane containing the ball of radius cos(w/2)>=sqrt(1-r²). Thus its inward-root site lies in that CLOSED half-plane. Equality is allowed: the sector angle may be pi and its triangle area zero. The fan from the site to the arc consists of the site/chord triangle plus the circular segment (w-sin w)/2, also in this limiting case.

For a boundary edge use §1's notation: z=m+t*n, U=m+ell*n, t<ell. If A is the opposite angle of the adjacent refined triangle, its third vertex lies on the inward side, so t=-(d/2)cot A. The paired cell area along [z,U] is (d/2)(ell-t)=d² cot A/4+(d/2)ell; the latter term equals sigma² sin(2b)/2. This establishes the boundary contribution with its sign, without requiring a convex hull edge of the full site set.

At each interior straight dual edge the paired site-edge area is d²(cot a+cot b)/4, with signed individual circumcenter offsets and nonnegative combined edge length; artificial zero-primal-length diagonals contribute zero. Reassembling each nondegenerate triangle's signed circumcenter pieces gives its ordinary area 2rho² sin A sin B sin C, whether acute or obtuse. A boundary switch contributes sigma² sin(2b)/2; the remaining ring cap contributes sigma_left*sigma_right*sin(alpha)/2+(w-sin w)/2. Therefore SHARED-FACTOR-DUAL's exact area identity follows by partition, not numerical testing. All genuine endpoint radii are positive; the certificate's closed zero-radius/zero-angle domains only enlarge their range.

Checks: primary source COMPATIBLE-EDGE-SUPPORT lines9,34-38; SHARED-FACTOR-DUAL lines7-19. The separate r20-gluing report corrected its gamma-at-switch misreading; the explicit equidistance argument above supplies the exterior-side sign rather than relying on that report's assertion.
