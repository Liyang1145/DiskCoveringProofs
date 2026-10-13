# k10 cover → triangulated disk → finite list: lead audit

## Scope
Unit closed disk D,14 equal disks radius0<r≤U=.33173203427623414, arbitrary centers. Project intoD, classify active iff meetingS1, merge equal hubs, apply same-arc inner-root replacement. This note is ONLY k10. C1142 gives3 or4 distinct hubs. No k11 essentiality/no-chord assumption is available; the85graph file for that branch is NOT an exhaustive reduction.

Inputs read: `BOUNDARY-OWNERSHIP-PROOF.md`, `../members/structure/NO-CHORD-n14.md`, `../members/topology/COVER-TO-DUAL.md`, and entire `gen_k10_catalogue.py`.

## Curved dual: verified analytic content, clarified details
Sites are distinct interior points of their convex clipped Voronoi cells. Every cell lies in its own radius-r disk by coverage. k10 no-chord means nonadjacent ring cells are disjoint. Exactly10 connected nontrivial boundary ownership arcs and their2-site switches are already proved. An interior Voronoi vertex is incident to≥3 cells. At most2 of them are ring cells, necessarily adjacent, so every vertex-star has a hub.

Build dual edges through facet-relative-interior midpoints, with straight radial segments inside each incident cell. Each ray from an interior site hits cell boundary only once; distinct facets give distinct rays. Thus no dual crossings, and no repeated edges (two convex cells share at most one facet). The10 edges for switch facets form a simple closed curve gamma, since their nonendpoint pieces are disjoint and all10 ring sites are distinct.

For each ring cell, the ownedS1 arc, the two outer half-facets, and the two dual half-edges enclose a sector disk in that cell. One detail missing in the earlier wording is why the remaining cell facets are on its inner side: radial projection from the site is a homeomorphism from the cell boundary to a circle of directions; the boundary subarc through the owned arc and the two switch points is precisely the outer half of that cyclic boundary, whereas every other facet midpoint is in the complementary subarc. The radial sectors therefore form an embedded closed annulus. The complement on gamma's bounded side contains all hub cells (disjoint from the sectors), so all hub sites and every non-ring dual edge are inside gamma. A hub cell cannot lie elsewhere outside gamma without lying in the annulus; its interior cannot intersect any ring-cell sector. Thus the exterior dual face has exactly the ring cycle as boundary.

Inside each cell, the dual spokes partition it into sectors indexed by its primal vertices; gluing sectors across primal facets gives one bounded dual face per interior primal vertex, and there is no other face. All sites incident at a primal vertexx lie on the empty circle centered atx with radius≤r. They are distinct and strictly convex in cyclic order; all fan triangles use the same witnessx. Abstractly fan each dual face from one of its hubs, realizing fan arcs inside the topological face. No ring chord is introduced (at most2 ring vertices, already adjacent). Actual curved faces need not be geometrically convex; the circle arrangement certifies common witnesses, while the topological disk certifies drawable fan arcs. Those are separate facts.

We have a simple triangulated disk with outer10-cycle,3 or4 interior hubs, no ring chords. Counts F=N+2m−2, E=2N+3m−3. ExactlyN triangles touch ring edges; the remaining2m−2 have≤1 ring vertex. Degenerate cocircular faces are handled by hub fans, not perturbation.

## Enumeration completeness: proof, not count calibration
LetH be the hub-induced graph. Label each face by its hub component (each face has≥1 hub and its hubs form a clique). Across an interior edge the two incident faces have a common hub, unless the edge is ring-ring; but all ring-ring edges are boundary edges. Face-adjacency connectivity of the disk implies every face has the same component, and every hub is in a face. ThereforeH connected.

For m≤4 the enumerated skeletons are ALL connected unlabeled simple graphs: m3=P3,K3; m4=P4,K1,3,C4,K3+pendant,diamond,K4. A hub-only triangle is a3-clique. Write h for their number, e for hub edges, f1 for1-ring triangles. Since f1+h=2m−2 and f1+3h=2e, h=e−m+1. Generator chooses every subset of exactlyh hub3-cliques and rejects those overusing an edge. In particularC4 cannot occur becauseh=1 but no3-clique.

For each ring vertexi, its link is a simple path from ringi−1 to ringi+1. Intermediate vertices are hubs, each appearing at most once. Removing the two ring endpoints leaves a possibly zero-edge simple hub path. Concatenating theseN hub paths cyclically is a closed walk. Each hub edge appears exactly2 minus its number of hub-only incident triangles. Thus the walk is an Euler traversal of the exact multigraph formed by these multiplicities. Generator enumerates every start and Euler traversal, then every weak composition of its edge count intoN path lengths; this includes the actual complex. It rejects repeated hub vertices within a ring link. Remaining edge-incidence/link/Euler tests hold for every genuine disk, so they cannot omit a valid cover. Duplicate walks are harmless.

Conversely the retained complexes have simple faces, boundaryN-cycle, links a circle/interior and path/boundary, connectedness, and Euler characteristic1; hence they are disks. Completeness needed only the forward implication.

## Concrete canonicalization bug found and repaired
Old generator uses reflected index `sh-(v-sh) = 2sh-v`, not `sh-v`. ForN=9 (odd),2sh runs over all residues: old56↔56 calibration cannot catch this. ForN=10 (even), only half the reflections occur. Worse, the incomplete transformation set is not closed under composition; its minimum is not a true canonical representative. This causes overcount, NOT missing coverage: each retained representative is still an actual dihedral/hub relabeling of the graph, and every graph was enumerated before deduplication.

A first partial fix testing only odd reflections also failed (nonclosed transformation set); discarded before use. Correct script `check_catalogue_symmetry.py` recomputes all2N×m! transformations from scratch. Results:
- m3:93 stored representatives → **68 true dihedral/hub classes**.
- m4:1442 stored representatives → **932 true classes**.
- k10 total: **1000**, not1535 isomorphism classes.
Corrected complete list: `k10-catalogue-corrected.json`; source indices retained. `catalogue-symmetry-audit.json` records duplicate groups. Old list remains a complete overinclusive list, but its claimed isomorphism count is false.

## Controls and reproducibility
1. `py -3 -B research-2026/next-cover-global/lead/replay_catalogue.py`: reruns entire generator budget10000sec (actual~28sec), exact set equality to old stored list, no budget exits. Evidence `catalogue-full-replay.json`.
2. `py -3 -B research-2026/next-cover-global/lead/check_catalogue_symmetry.py`: full canonicalization, corrected list1000.
3. `py -3 -B research-2026/next-cover-global/lead/audit_catalogue.py`: independent edge/link/Euler checks on all1535 stored complexes. Also computes exact rational circumcenter nearest-site tests for new literal construction (finite candidates kernel only used for generation), finding16 actual Voronoi triangles; its graph matches old10/4 index1394, skeletondiamond. Ring ordering proposed by atan2, consecutive orientation then checked rationally. This is a candidate identity/control, not a completeness proof.

## Limits
The graph carries incidence and shared radius-r witnesses only. This necessary relaxation need not be sharp: an obtuse Voronoi triangle can have a smaller enclosing ball than its circumradius. Any sharp stress bound using free witnesses must audit this distinction. No one of1000 metric exclusions has been proved here. k11 remains outside this reduction. Exact optimum and unrestricted lower bound remain open.
