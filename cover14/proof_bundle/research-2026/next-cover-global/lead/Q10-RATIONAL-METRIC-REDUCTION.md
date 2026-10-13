# Rational normalized metric domains and exterior stripping

## Object and invariant
Only q10/879 remains by C1330. Fix exact U=.33173203427623414, L=2asin(U), D=10L−2pi>0. Production anchors have angles phi_j=jL−sum_{i<j}d_i. Every admissible deficit vector lies in d>=0, sum d=D. The newer necessary cuts all have rational coefficients and right sides rational multiples of D. Setting x=d/D converts ALL such polytope geometry to rational arithmetic. No interval zero test is needed to determine this normalized domain.

## Independent complete clipping
`q10_rational_polytope_audit.py` does not import the producer's clipping routine. Given a complete vertex set V, with equality sum x=1 and inward inequalities n·x>=b:
1. Check feasibility and full active rank10 at every vertex.
2. For each pair strictly on opposite sides of a new hyperplane, find their common active constraints. The smallest face containing both has affine dimension 10−rank([equality;common active normals]). Thus rank9 is exactly an edge.
3. Interpolate the crossing point with exact Fraction scalar t=s_u/(s_u−s_v). Check all original inequalities and exact new hyperplane equality.
4. Each child has precisely its original on-side vertices plus these crossings. This standard hyperplane clipping statement includes all old vertices on the cut and degenerate crossing coincidences; coincident crossings are deduplicated. Closed opposite children cover the entire parent.

The first combined C1331/C1332 root has184vertices. Its independent all-support enumeration (`q10_reduced_domain_audit.py`) uses sum x=1 and6 extra cuts: a vertex with k positive coordinates needs k−1 independent active extra cuts, hence k<=7. Enumerating all supports and all sets of k−1 cuts proves completeness, not just feasibility of a supplied list. Later roots are exact successive clips of this root. The producer uses Q³ module coordinates and active-system reconstruction; the scalar audit uses rational edge interpolation. Shared generic rational rank arithmetic is explicit, not an independence claim about every helper.

## Leaf inference
For an exactly force-balanced nonzero rational flow z on every original site–face-witness and anchor–site incidence, every feasible radius r obeys r >= L_z(A)/sum_e||z_e||. The leaf certificate uses a concave minorant in affine anchor angles and checks it at every complete polytope vertex. Endpoint nonnegative radial terms yield concavity; otherwise a global quadratic correction supplies a concave minorant. `q11_chord_flow_fraction_replay.py` rebuilds original graph incidence, owners, force balance, norm upper bounds, angle intervals, endpoint signs, and all vertex lower bounds in Fraction arithmetic. Optimizer success and displayed decimals bear no inference. Exact leaf lower>U excludes the whole closed leaf.

## Exterior-to-domain inference
A closed exterior slab excluded over the CURRENT globally necessary domain supplies the opposite STRICT inequality for every feasible879 system. Only after excluding all leaves of the exterior tree can that inequality be used. A partial tree or unsuccessful root bound supplies no such cut. Automorphisms must permute the actual16faces and20anchor incidences, with deficit map i -> perm(i+1)−1; reflection reverses anchor cyclic order but preserves distance feasibility. This is finite transport, not symmetry WLOG.

## Source-bound artifacts
- C1332 first triple cut: q10-fan-leaf-audit.json + q10-fan-transport.json.
- C1333: q10-metric-slab-audit.json + q10-slab-transport.json.
- C1334: q10-tight-slab-audit.json.
- C1337: q10-c1334-slab-audit.json (filename names INPUT domain).
- C1341: q10-exterior-union.json, three complete5node/3leaf trees.
- C1348: q10-large-union.json, one leaf plus three complete3node/2leaf trees.

Root domains and unions record source hashes; later generations have separate filenames. The historical157node fulltree snapshot remains untouched. Tree counts are bookkeeping only; progress is the actual necessary metric region removed.

## Final transport provenance and downstream bridge
`q10_cut_transport_provenance.py/.json` independently checks all round2..8 cut lists, four actual16-face/10-owner-pair graph automorphisms, owner-deficit maps, source hashes, rooted trees with exactly two children per split, pending/open matches, leaf-index matches and saved lower>U. Closed-case counts are5,3,3,2,3,2,2 and transported-cut counts16,10,10,6,12,4,8. This is structural/source validation, NOT a rerun of leaf arithmetic or root-polytope completeness.

Round8's two fully closed exteriors (cases0,2) correctly give8 cuts via the four automorphisms. The audit source explicitly loops `for g in autos` inside `if not pending`; no rotated tree files are required. If S is ANY feasible full879 system, its automorphic image is again feasible and therefore lies in the globally necessary parent domain. Applying a base cut to that image proves the transported cut for S. Parent-domain geometric invariance is not needed for this inference; global necessity is. The transport file's source hash binds its original leaf certificate, not a later domain, and the reusable automorphism is certified by incidences rather than that hash.

The old missing implication from this domain to a local cell is now supplied by C1371 (direct halfspace-dual angle box) and C1370 (balanced-flow uniform quadratic minorant), followed by C1355's effective2e-6 anchor-cell theorem. See `Q10-QUADRATIC-GLOBAL-BRIDGE.md`. Under ordered once-winding circle anchors, C1281 supplies witness-to-cover sufficiency. Interval residuals containing0 and arc sums containing2pi are never exact-equality proofs. Original-goal completion awaits final assembly of the audited full chain.
