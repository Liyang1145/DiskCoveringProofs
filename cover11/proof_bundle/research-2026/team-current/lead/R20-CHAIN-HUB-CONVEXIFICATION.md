# Whole-chain hub convexification from the two boundary-circle roots

Status: analytic derivation; independent geometry audit requested. This is a fixed-ring conditional equivalence for each fan, NOT a global optimum or complete cover criterion. It does not impose symmetry, equal boundary arcs, saturation of triangle radii, or flatness.

## Legal ring interface
Fix 0<r<1, two distinct ring centers a,b in int D, their radius-r disks. Assume their actual covered unit-circle arcs have exactly ONE equal-distance point U in their common covered arc. This holds for neighboring essential arcs in the established nine-arc ledger: noncontained proper arcs, unique switch. In a full cover hubs satisfy STRICT |h|<1-r. The latter strictness is used and must not silently be changed to closed H.

Let m=(a+b)/2, e=(b-a)/d, d=|b-a|, A=d/2. Their radical line is m+tn with n perpendicular e. Choose n so U=m+t+ n is the positive unit-circle intersection, t+>0; since |m|<1 the other boundary intersection has t-<0. Define k=sqrt(r²-A²).

### Lemma 1: two ring-circle roots, one inside and one outside D
At U, |U-a|²=A²+t+²<=r². Thus k>=t+>0, so d<2r. The other unit-circle intersection V=m+t- n cannot be covered by both disks: it would be a second equality point in the common covered arc, contrary to the hypothesis. Hence A²+t-²>r² and t-<−k. Consequently
 p_in=m−kn lies STRICTLY inside D,
 p_out=m+kn lies outside int D (possibly on boundary).
No strict overlap is required: if U is the common arc endpoint, t+=k and p_out=U. Tangency of the two ring circles (k=0) is impossible under these hypotheses.

### Lemma 2: circumradius crescent formula
For any noncollinear h=m+x e+y n, the squared circumradius of triangle(a,b,h) is
 rho²= [((x+A)²+y²)((x−A)²+y²)]/(4y²).
Using k²=r²-A²,
 4y²(rho²-r²)
 =[(x²+(y-k)²-r²)][(x²+(y+k)²-r²)]
 = (|h-p_out|²-r²)(|h-p_in|²-r²).
If |h|<1-r then |h-p_out|>=|p_out|-|h|>r. Thus for ANY noncollinear strictly interior hub,
 rho(a,b,h)<=r iff |h-p_in|<=r.
Moreover disk membership itself forces y<0: for y>=0, distance to p_out is no larger than distance to p_in, contradicting the strict exterior condition. Hence no extra side constraint is needed and no collinear h belongs to this feasible lens. Conversely rho<=r forces the disk condition and then the inward side automatically.

### Corollary: eliminate all chain face inequalities together
For a fixed four- or five-edge sequence of neighboring legal rings c_i, define p_i as the interior intersection of their radius-r circles. Then a strictly interior hub h satisfies ALL corresponding triangle-circumradius constraints iff
 h in B_open(0,1-r) intersect intersection_i B_closed(p_i,r).
This set is convex; orientation/noncollinearity follow automatically. All chain-internal radius parameters and inequality branches are eliminated, with no assumption that rho_i=r. Candidate contact is NOT used to prove this statement.

A nonempty closed relaxation B_closed(0,1-r) intersect intersection_i B_closed(p_i,r) is only a NECESSARY condition unless a strictly interior point is exhibited. At |h|=1-r and |p_out|=1, the strict exclusion can fail, so retain strict norm or audit equality degeneracies separately.

## Implication and remaining obligations
Under q0(6,7), the two four-/five-edge fan chains give two such convex feasible hub sets, depending on the nine ring centers and r. This removes generic nonconvex circumradius crescents for those nine faces. The two central triangles (hA,hB,c0) and (hA,hB,c4), their common-side compatibility, Delaunay/triangulation validity, ring boundary constraints, and global variable control remain. Independent feasible chain hubs do NOT automatically imply a whole cover. Nor does failure at the candidate rings imply global failure. Future useful target is eliminate pair(hA,hB) over these two convex sets while retaining the two central faces.

## Relation to historical work
HUB-CONVEX-LENS-REDUCTION.md already convexifies the special flat C848 local two-face situation. C456/C458/C466 give a different split-residual representation. The present interface applies to arbitrary neighboring essential ring arcs and an entire nonflat chain via radical-line root ordering. Search/audit required before claiming novelty; none claimed.
