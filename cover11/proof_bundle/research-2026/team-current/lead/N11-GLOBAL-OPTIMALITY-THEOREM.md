# Global optimum for eleven congruent disks covering a unit disk

Registered result: **C924**; unrestricted reduction: **C923**. These registrations record the proof below and its dependencies; registration itself is not certification.

## Theorem
Let D={x in R²: |x|<=1}, and let r_D(11)=inf{r>=0: D is contained in the union of eleven closed radius-r disks with arbitrary centers in R²}. Then

**r_D(11)=R\***,

where R* is the exact isolated root coordinate defined below. In particular,

0.3799838531198386897222616061358 < R* < 0.3799838531198386897222616061364.

These finite decimals are rigorous outward bounds, not the definition of R*. The theorem is unconditional with respect to configuration class: no symmetry, nonoverlap, prescribed contact graph, general position, or boundary saturation is imposed on competing covers. The proof is analytic plus computer-assisted exact rational/directed interval certification. It is not a proof-assistant formalization or an assertion of external peer review.

## Exact definition and an attaining configuration
Write z=(a0,a1,a2,a3,y0,y1,R), a4=pi-2(a0+a1+a2+a3), and a=(a0,a1,a2,a3,a4,a3,a2,a1,a0). Set theta4=0 and theta_(k+1)-theta_k=a_k+a_(k+1), with periodic lifts. Define

rho_k=cos(a_k)-sqrt(R²-sin²(a_k)),
C_k=rho_k(cos theta_k,sin theta_k), H0=(y0,0), H1=(y1,0),
B_k=(cos(theta_k+a_k),sin(theta_k+a_k)), U_k=C_k+C_(k+1)-B_k.

All square roots take the positive branch. Let f(z) have first four components |U_k-H_j|-R for (k,j)=(1,1),(2,0),(3,0),(8,1). Its fifth component is |W-C6|-R, with m=(y0+y1)/2, d=(y1-y0)/2, W=(m,sqrt(R²-d²)).

The twelve equations are f(z)=0 and e_R-Df(z)^T lambda=0. The exact solution is the unique solution in the rational dyadic box with center `certificate.center_hex` and common halfwidth `certificate.radius_hex` of `repaired_tc_krawczyk.json`. Hex strings are interpreted as exact binary rationals. R* is z[6]. C891 proves existence/uniqueness in this box; uniqueness outside this box is not asserted. `repair_tc_krawczyk.py` and the independent expression-tree interval audit establish its isolation, not just a numerical Newton solve.

The eleven centers C0,...,C8,H0,H1 at this root cover D with radius exactly R*: boundary arcs tile, nine active circumradii equal R* by the exact equations/reflection, and two are strictly smaller. The eleven strict empty-circle faces form the complete Delaunay triangulation, so the boundary and Voronoi critical-point test certifies all of D. Evidence C892, `STRICT-EMPTY-FACET-COMPLETENESS.md`, `check_tc_root_geometry.py`, `tc_root_geometry.json`.

## Lower-bound proof
Assume a cover with r<R*. The same-root enclosure C922 gives R*<19/50.

1. **Arbitrary cover to an embedded two-hub graph.** The two-circle weighted capacity certificate C450 excludes ten boundary disks plus one other disk. Arc capacity and coverage of the origin then force exactly nine boundary disks and two strict indispensable interior disks. Replacing outer radial roots by the inner roots of the same actual arcs preserves coverage. Rebuild nearest-site ownership afterward. Essentiality makes nine connected owned arcs with distinct two-site switches. The two full hub cells must share a positive edge: otherwise one hub cell contains the core, and its radial facets force nine ring disks to violate the stronger per-disk C450 two-circle capacity bound. The clipped dual is an embedded disk, and its straight realization follows from selected Delaunay polygons. Refinement diagonals retain genuine nearest witnesses; they are not asserted to have positive primal length.
2. **Exhaust all topologies.** Ring locality forces every ring chord to skip only one vertex. The long-side incidence count forces such a chord to cut off an empty ear. Two ears contradict arc-capacity/star bounds, so q<=1. Deleting ears leaves two complementary hub fans; the hub-degree sum is13-q. Full-domain metric certificates exclude degree3, all q1 degree pairs (4,8),(5,7),(6,6), and q0 pairs (4,9),(5,8). Thus only q0(6,7) remains. These certificates apply to actual r<=19/50 geometry normalized by19/50, not to an assumed saturated replacement at19/50.
3. **A one-way convex oracle relaxation.** Relabel the surviving graph with hub9 fan edges0..3, hub10 fan edges4..8, and central faces(9,10,0),(9,10,4). The nine boundary switches are fixed anchors. Eleven site nodes plus eleven face-witness nodes are free. The eighteen endpoint edges and thirty-three face edges all have length<=r in the true cover; hence its oracle optimum V(U)<=r. Witnesses remain actual nearest vertices in this implication; the relaxed oracle does not require them to be circumcenters.
4. **The entire angular domain.** With L=2asin(19/50), D0=9L-2pi, every owned width Delta_i<=L yields y_i=(L-Delta_i)/D0>=0 and sum y_i=1. After rotation theta_i=iL-D0 sum_(j<i)y_j. No symmetric subspace is imposed. C921 proves V(U(y))>=R* on this entire closed eight-dimensional simplex. Positive normalized stress energies minimized over all free nodes are lower bounds for V². Exact rational Schur elimination and whole-interval cosine minorants certify 2386 energy leaves. The other120 leaves lie in the proved C919/C920 angular balls about the same exact root, using full mixed-direction Taylor remainders. Exact DBM splits cover the simplex. The exact threshold T used by energy leaves is strictly greater than R* by C922.

Consequently R*<=V(U)<=r<R*, a contradiction. Together with exact attainment this proves the theorem.

## Bearing evidence and reproducibility
`UNRESTRICTED-PROOF-ASSEMBLY.md` contains the detailed interfaces, complete graph-class ledger, degeneracy treatment, sources and final replay provenance. `FINAL-PROVENANCE-AUDIT.md` records arithmetic and analytic reconciliation. In the paths below, L denotes `research-2026/team-current/lead/` and S denotes `research-2026/solo-20260922/` (expand these path prefixes when running commands).

- Root/attainment: `py -3 -B L/repair_tc_krawczyk.py`, `py -3 -B L/check_tc_root_geometry.py`, `py -3 -B L/contract_exact_root_threshold.py`.
- Two-circle atom: `py -3 -B S/verify_directional_fixed.py`, `py -3 -B S/verify_directional_fixed_low.py`, `py -3 -B S/audit_dual_manifest.py`.
- Metric classes: `py -3 -B L/replay_q1_final.py`, `py -3 -B L/replay_upstream_certificates_r23.py`; their JSON manifests list all commands, hashes, return codes and logs. The proof also requires their analytic geometric domain and dual-identity derivations, not merely return codes.
- Local stress balls: `py -3 -B L/certify_anisotropic_stress_ball.py`, `py -3 -B L/certify_relative_stress_ball.py`.
- Global oracle: `py -3 -B L/replay_closed_dbm.py`, `py -3 -B L/replay_all_fields.py`; direct local containment: `py -3 -B research-2026/team-current/r20-rigidity/r20_direct_patch_replay.py`.
- Final tree SHA256: `6706b42690a1d99d8f49523ff0d7d82fbc688fd64a18b228512acec139aef987` (`cosine_dbm_local920.json`). All371 normalized rational fields are rederived exactly; 2505 exact splits,2386 energy leaves,120 direct local leaves,zero open leaves.

## Scope limitations
No global uniqueness classification of optimal configurations is proved here. No n=14 optimum is claimed. Historical notes headed 'pending' or 'not global' retain their original local scope and timestamps; the unrestricted theorem follows from this assembled reduction, not by silently broadening those notes. No mathematical implication remains identified as open in this n=11 proof; external verification and publication-quality exposition remain valuable separate work.
