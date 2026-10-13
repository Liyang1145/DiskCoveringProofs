# Fixed boundary switches: a convex network oracle and an eight-angle global obligation

## 1. Explicit input graph and quantifiers
Unit disk, radius r≤19/50. Assume the established canonical 9-ring+2-hub q0(6,7) reduction, with an embedded refined nearest-site dual disk. Label ring sites c0,...,c8 cyclically. Without loss of cyclic relabeling/reflection, hub a fans over ring edges0,1,2,3, hub b over4,5,6,7,8; the two central faces are (c0,a,b),(c4,a,b). Thus 11 triangular faces. Ui denotes the nearest-cell boundary switch between ci and c(i+1), not the center-angle bisector. Each ci owns the boundary interval from U(i−1) to Ui.

## 2. Fixed-switch convex oracle
For fixed unit anchors U=(U0,...,U8), put free variables C=(c0,...,c8,a,b)∈R22, Z=(zf)∈R22 and t≥0. Define V(U) as the minimum t subject to
- |ci−U(i−1)|≤t and |ci−Ui|≤t for each i (18 constraints);
- |cs−zf|≤t for each of three vertices s of each face f (33 constraints).
This is a second-order cone program. In particular zf is FREE, not defined as the circumcenter. The feasible set is convex without any acute assumption. A true cover in this graph supplies a feasible point with t=r: choose its sites and zf the original interior Voronoi vertex of the refined face. All incident sites are equidistant from this vertex with distance≤r; boundary switch incident sites likewise have distance≤r. Therefore V(U)≤r.

Oracle solutions need NOT have the intended embedding, legal inward rings, distinct sites, or even cover D. These omitted constraints only relax the problem and preserve the direction of the lower bound. No inverse implication is required.

Existence/strong duality: the finite graph is connected to fixed anchors. If t is bounded, all free nodes are bounded by following graph paths to an anchor. Feasibility is closed, so the finite optimum is attained. Set all free nodes to0 and choose t>max_i|Ui|+1: every inequality is strict and t>0. Slater yields strong conic duality.

## 3. Vector-force lower certificates
Orient every edge e=(v,w). Let Xe=Xv−Xw, where fixed node coordinates are Ui. Choose vectors pe∈R2 satisfying divergence0 at EVERY free node and Σe|pe|≤1. Then any feasible point obeys
Σe pe·(Xv−Xw) ≤ Σe|pe| |Xv−Xw| ≤ t.
Free-node terms cancel exactly. Writing li for the signed sum at anchor i, obtain
V(U)≥Σi li·Ui.
Conversely the supremum of these expressions is V(U), by the SOCP dual and Slater. For a one-free-node/two-anchor subgraph, opposite vectors of norm1/2 give |U−W|/2, calibrating the sign and budget. Distinct anchors cannot all be collapsed onto a single free node, so the previously reported dual-zero argument was erroneous.

The feasible force set is compact and independent of U. Thus V is convex and positively homogeneous in the CARTESIAN anchor coordinates, continuous, and invariant under simultaneous rigid Euclidean motions (rotation and translation). Convexity does NOT extend to the unit-circle angular parameter domain.

## 4. Angular domain genuinely covering all true covers
A radius-r disk with r<1 covers either an empty or a single short unit-circle arc of length at most2asin r. Indeed writing a nonzero center as d(cosφ,sinφ), coverage is cos(θ−φ)≥(1+d²−r²)/(2d)>0; the right side is at least sqrt(1−r²). The center0 covers no unit-circle point. Its connected owned interval is contained in this short arc. Consequently its width Δi satisfies 0<Δi≤2asin r. This uses inclusion of the WHOLE owned interval, not merely the endpoint chord inequality (which alone cannot exclude a major arc).

Set L=2asin(19/50). Since ΣΔi=2π, all Δi≥m=2π−8L>0. Positivity is exact because 19/50<sin(π/8) (square using sin²(π/8)=(2−sqrt2)/4). Thus all true switch lists, modulo rotation, belong to the compact 8D polytope
P={Δ∈[m,L]^9: ΣΔ=2π}.
One may fix one anchor at(1,0), with the others obtained by cumulative widths in cyclic order. The lower width bound follows already from sum and upper caps; it introduces no additional relaxation. Essentiality does not remove a Δ=0 boundary here, because such boundary points do not exist in P. Hub disks, being strictly interior, cover NO unit-circle switch: no hub-to-switch constraints may be added.

## 5. Exact candidate sharpness: the outstanding small interface
Suppose an exact candidate has the C897 normalized positive minimax KKT relation on nine active tie-radius functions and nine active triangular circumradius functions, plus two slack triangles. If its active triangles are acute and each active tie has opposite nonzero tangential distance slopes, that relation lifts to a SOCP KKT certificate:
- Active face f, circumcenter zf=Σs βfs cs with βfs>0, Σβfs=1: the site derivative of Rc equals βfs(cs−zf)/R. Put force weights νf βfs on the three unit-distance gradients. The zf balance is exact by the barycentric identity. Slack-face forces0.
- Active tie between c,d at U with tangent T=JU. Set sc=((U−c)/R)·T and sd=((U−d)/R)·T. Differentiating equal distances gives dρ=α[(c−U)/R]·dc+(1−α)[(d−U)/R]·dd where α=sd/(sd−sc),1−α=−sc/(sd−sc). Opposite slope signs imply α,1−α>0. Split its KKT weight μ by these fractions. Equal halves are NOT generally valid.
- Site force balances are exactly the physical KKT identity, and total force norm is Σμ+Σν=1. Every force-bearing edge has lengthR. Hence the dual objective is exactly Σe pe·Xe=R, not merely close numerically. Together with candidate feasibility, V(U*)=R.

The exact acuteness/slope interval premises at the C891 root are being checked separately. Numeric SLSQP agreement at rounded saved anchors is only evidence, not the equality proof. C907 supplies joint-hub convexity in a separate nominal ring box; it does NOT by itself identify U* or certify this full candidate lift.

## 6. The main remaining implication
If one proves V(U(Δ))≥R* for EVERY Δ∈P, then every true covering configuration with r<R* is excluded by the earlier class reductions and §2. With the exact candidate cover C892 this proves r_D(11)=R*. This is an eight-angle GLOBAL lower-bound obligation with a convex 45-variable inner oracle, not an assumption that the cover itself is symmetric. The graph may be fixed only after the q0(6,7) reductions; all other classes are excluded by their own bearing dependencies.

If the oracle is strictly belowR* at some distant anchor tuple, this disproves only this global relaxation inequality, not covering optimality. A local sharp certificate, analytic KKT at U*, finite-direction increases, or convexity in Cartesian anchors alone does not solve the outer problem.
