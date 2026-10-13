# Exact endpoint-lens elimination for q10/879

Route: independent analytic reasoning, route unverified. Read root STATUS.md and DEAD.md before exploration. This is a bounded analytic result, not a subdivision run or an optimality assertion. All new files are in this member directory.

## Result and precise scope

**Proved analytic reduction:** for the abstract radius-r anchor/face incidence system of `lead/k10-catalogue-corrected.json`, entry `10/4[879]`, all 16 free face witnesses and the four sites **3,8,10,12** can be eliminated exactly. At fixed anchors this removes eight site coordinates, leaving the eight other boundary owners and hubs 11,13. The replacement is four finite disjunctions of explicit scalar inequalities; there is no optimization over the eliminated sites. The central diamond is retained, not replaced by independent edge-length bounds.

Quantifiers: arbitrary r>0; arbitrary fixed planar coordinates of the ten retained sites; arbitrary fixed anchors (in the intended application ordered on the unit circle). The reduction is an **if and only if for the incidence system**. For actual disk covers it gives necessary conditions only: reconstructing abstract face witnesses does not prove empty-circle, planar embedding, orientation, or coverage. No symmetry WLOG and no assumption that owners lie at inner lens vertices.

The original unrestricted sharp n14 optimum remains open. The current U is the exact decimal 0.33173203427623414, not an exact definition of the sharp optimum. No stronger numerical radius lower bound is claimed.

## 1. One triple reduced to scalar inequalities

For sites a,b,z in R² put

    A=|a-b|², B=|a-z|², C=|b-z|²,
    M=max(A,B,C), S=A+B+C, J=det(b-a,z-a).

Let T_r(a,b,z) mean that there exists a point w at distance at most r from all three sites. Exactly:

    M <= 4r², and
    [ 2M >= S  OR  ABC <= 4r² J² ].                 (1)

In the first branch the triangle is right/obtuse/collinear, and its minimum enclosing disk has radius sqrt(M)/2. This includes duplicate points. In the other branch the triangle is acute, so the minimum enclosing disk is its circumdisk, with squared radius ABC/(4J²). An acute triangle has J != 0. One proof of this familiar characterization is to take a minimum enclosing disk: if supported by two points they are antipodal and give a diameter; otherwise it is supported by all three and their center lies in their convex hull. Thus (1) also handles all degeneracies, without divisions or a near-zero-area decision.

This is stronger than the three pairwise distance inequalities. Exact rational control: a=(-9/10,0), b=(9/10,0), z=(0,8/5), r=1 has all three squared distances <=4 but fails the acute branch of (1). Hence this reduction does not discard the face-radius condition in favor of graph-edge distances.

## 2. Endpoint-lens offset has at most four boundary circles

For fixed a,b define the allowable third-site locus

    K_r(a,b) = {z:T_r(a,b,z)}
             = (B(a,r) intersect B(b,r)) + B(0,r).  (2)

The equality is immediate by using the common face witness w in both directions. This is a compact convex set, or empty if |a-b|>2r.

If d=|a-b| satisfies 0<d<2r, let

    m=(a+b)/2, h=sqrt(r²-d²/4),
    c_±=m ± (h/d) R90(b-a).

The boundary of K is made of arcs from the four supporting circles

    (center a, radius 2r), (center b, radius 2r),
    (center c_+, radius r), (center c_-, radius r). (3)

Here a supporting circle means a circle containing a boundary arc, **not** an assertion that K is the intersection of its four disks. The latter assertion would be false.

Proof: the endpoint lens has two circular arcs, centered at a and b, meeting at c_±. Offsetting its smooth arcs outward by r doubles their radii. The exterior normal cones at its two vertices produce arcs of radius r centered at c_±. Equivalently, for any unit normal n, the support point of the Minkowski sum is the unique support point of the lens plus rn; on smooth arcs that point is a+2rn or b+2rn, and at a lens vertex it is c_±+rn. These normal regimes cover all directions.

Degeneracies are explicit:

* d=0: K=B(a,2r), one boundary circle.
* d=2r: the lens is {m}, so K=B(m,r), one boundary circle.
* d>2r: K is empty and the corresponding test fails immediately.

## 3. Finite intersection lemma (no unknown hub)

Let Q_1,...,Q_k be nonempty sets, each either an ordinary positive-radius closed disk or a set K from (2). Collect the boundary circles described above, deleting exact duplicates if desired. Write them as (p_i,R_i), i=1,...,N. Form a finite candidate set V consisting of:

1. p_i+(R_i,0), the rightmost point of every circle;
2. both intersection points of each pair of distinct noncoincident circles, when they intersect (one point for tangency).

Then

    intersection_j Q_j != empty
       iff there is v in V with v in every Q_j.     (4)

The scalar membership test is (1) for K and |v-A|²<=r² for an anchor disk. The set V has at most N+2 binom(N,2)=N² points, including duplicates. In particular this is a finite test, not a search over a free planar center.

**Proof.** The reverse direction is immediate. For the forward direction maximize the first coordinate on the compact nonempty intersection, giving p. At least one Q_j is active at p, and p lies on one of its boundary circles. If p belongs to two distinct supporting circles, it is a pair-circle candidate. Otherwise all active boundaries at p locally coincide with one circle (circle-arc junctions would themselves belong to two distinct circles). The inactive constraints have positive slack. Locally the intersection therefore agrees with the inward side of this one circle. Its first coordinate can be locally maximal only at the circle's rightmost point, which is candidate 1. This argument also covers a singleton intersection: a singleton cannot arise locally from just one positive-radius disk boundary, so it falls under the multiple-circle case. Exact coincident circles do not create a missing case; they define the same local inward side.

For explicit radical generation, for two circles (p,R),(q,S) with t=|q-p|>0 and |R-S|<=t<=R+S, put

    x=(t²+R²-S²)/(2t),
    b=p+(x/t)(q-p),
    v_±=b ± sqrt(R²-x²)/t * R90(q-p).               (5)

Use the nonintersecting/coincident branches separately. All comparisons here are exact mathematical comparisons; toleranced code below is only a calibration.

## 4. The graph has a four-site exact face transversal

Inspection of the actual catalogue gives the following partition. **Every face contains exactly one vertex of {3,8,10,12}.** There is no face coupling any two eliminated sites.

For retained sites x_i, abbreviate K(i,j)=K_r(x_i,x_j). Define

    H10 = K(0,1) ∩ K(0,9) ∩ K(1,2)
          ∩ K(2,11) ∩ K(9,13) ∩ K(11,13),

    H12 = K(4,5) ∩ K(4,11) ∩ K(5,6)
          ∩ K(6,7) ∩ K(7,13) ∩ K(11,13),

    H3  = K(2,11) ∩ K(4,11) ∩ B(A2,r) ∩ B(A3,r),

    H8  = K(7,13) ∩ K(9,13) ∩ B(A7,r) ∩ B(A8,r). (6)

Production anchor convention is exactly that of C1331: A_j is incident to owners j,j+1 mod 10; owner i has endpoint anchors A_{i-1},A_i. Hence the anchor disks in H3 and H8 are indexed as above.

**Exact reduced system:**

* For each retained boundary owner i in {0,1,2,4,5,6,7,9}, require |x_i-A_{i-1}|<=r and |x_i-A_i|<=r.
* Require all four sets H10,H12,H3,H8 to be nonempty, using the finite scalar tests (4).

These conditions are equivalent to feasibility of all 20 original anchor-owner incidences and all 16 face-witness triples for some x3,x8,x10,x12 and some face witnesses. Necessity follows from (2). For sufficiency select a point independently in each H, then select the separate common witness guaranteed by each K membership. The selections do not conflict because every face has exactly one eliminated vertex. The retained owner's anchor constraints and the disk factors in H3,H8 provide every boundary incidence. This proves the full quantified equivalence, not merely four independent necessary hub conditions.

The central faces (10,11,13) and (11,12,13) appear through the shared K(11,13) in H10 and H12. Its actual coordinates remain shared; one must not give these two factors different retained x11,x13.

Counts at fixed anchors: 14 sites initially give 28 real coordinates (plus 32 face-witness coordinates if kept). The reduced system has 10 sites, hence 20 real coordinates and no face witnesses. H10,H12 need at most 24 circles and 576 candidates each; H3,H8 at most 10 circles and 100 candidates each. These are finite worst-case counts, not performance claims. Each nonemptiness test can be evaluated separately; no Cartesian product of candidate sets is needed.

At the anchor level retain theta_j=L-d_j, L=2asin U and sum d_j=D. This reduction does not use or weaken the supplied C1332/C1333 cuts; they can be imposed concurrently. It applies also at saturated owner gaps d2=d7=0, where H3/H8 include tangent anchor disks. No division by those deficits is made.

## 5. Evidence and calibration

* Analytic proof: Sections 1–4 above; no numeric premise is bearing. An explicitly routed fresh `subagent_judge` audit was attempted: the first job failed with no report; one retry returned no report during its bounded audit wait and cancellation was requested. No independent audit verdict or verified underlying model route is claimed.
* Graph source: `../../lead/k10-catalogue-corrected.json`, exact entry `10/4[879]`. The code independently extracts the endpoint lists, checks the four faces remaining after hub10/12 elimination, and checks that every catalogue face hits {3,8,10,12} exactly once.
* Repro: `py -3 -B research-2026/next-cover-global/members/q10-analytic-second/elimination_controls.py`.
* Output: `controls.json`. Six Fraction-arithmetic triple controls and five bounded floating intersection controls cover duplicate endpoints, d=2r, circle tangency, empty intersections, a nondegenerate lens, and failure of pairwise-only face checks.
* Saved candidate: frozen `lead/improved-upper-test.json`, relabeled using the first exact catalogue match. At U, with float tolerance 1e-13, both saved hubs pass; the finite tests also find feasible candidate points near (0, ±0.3886186967982857), 466 generated candidates per hub. The owner3/8 factors also pass and find points near (±0.94337365737811,0), with 88/90 generated candidates; their anchors are read from `lead/stress-barycentric-result.json` and relabeled using the same match. These are **numeric calibration only**, not exact feasibility certification. Existing candidate certification is not rerun or replaced.

## Remaining implication and one next action

The exact parameter reduction does **not** show that all reduced feasible systems have r>=r*. It leaves eight owner positions, two central hubs and the anchor metric. Also, abstract incidence feasibility is weaker than actual coverage. The previously proved fixed sharp Dirichlet-energy impossibility is respected; nothing here asserts convexity of a sharp energy.

**One next action:** derive an analytic lower bound for the reduced shared-hub system (6), particularly the simultaneous H3/H8 and H10/H12 constraints with the same x11,x13. Any proposed bound must hold on all finite candidate branches, including tangent anchor lenses, without selecting the candidate's symmetric branch WLOG. The immediate closed result is the exact four-site elimination, not that remaining lower bound.
