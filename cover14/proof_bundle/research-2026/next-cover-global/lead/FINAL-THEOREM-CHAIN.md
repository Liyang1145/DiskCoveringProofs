# n14 unrestricted optimum — assembled analytic/computer-assisted proof

## Original objective
Cover the closed Euclidean unit disk by 14 congruent closed disks with completely arbitrary centers in R². Prove the exact minimum radius, an attaining configuration, and impossibility at every smaller radius. No prescribed symmetry, topology, or general position.

## Proposed exact value (already attaining: C1167)
Define (z*,c*,r*) as the unique zero in the explicit rational isolating box of `root-integer-certificate.json` of F=G=H=0 below, with all square roots positive:

s=sqrt(1-r²), a=(s+z)/2, t=r+sqrt(r²-z²), b=r+sqrt(r²-(a-z)²), d=1-sqrt(r²-c²),
v1=(1+a²+b²-r²)/2, v2=(1+c²+d²-r²)/2, det=ad-bc,
F=(v1*d-v2*b)²+(a*v2-c*v1)²-det²,
G=((a-c)²+(b-d)²)*(c²+(d-t)²)*(a²+(b-t)²)-4*r²*((c-a)*(t-b)+(d-b)*a)²,
H=F_z*G_c-F_c*G_z.

The isolating box, not the printed decimal, fixes the branch exactly. A safe rational enclosure follows immediately from that box:

0.33173203427623412254 < r* < 0.33173203427623412257 < U=0.33173203427623414.

The 14 centers are (±a,±b), (±c,±d), (±s,0), (±z,0), (0,±t); independent signs in each four-point orbit. `ROOT-ATTAINMENT.md` proves entire-disk coverage, not just boundary/contact coverage, including enumeration of all potential interior nearest maxima and exact active identities.

## Lower-bound chain (proposition interfaces)
1. Given any cover with radius r<r*, necessarily r<U. Radius zero is immediately impossible for a finite collection of singleton disks.
2. Project/normalize arbitrary centers without losing coverage, merge duplicates if any, and use positive boundary ownership, outward clipping, and a compact limiting argument. C1171 produces a finite necessary Cartesian graph witness system, allowing degeneracies and hidden boundary singleton cells.
3. The complete graph exclusions summarized by C1330 leave only q10/m4 catalogue879. This is a necessary reduction, not a symmetry assumption.
4. The source-bound rational exterior exclusions through C1366 force normalized deficits x into the closed halfspace outer domain. Strict necessary cuts may safely be relaxed to this closed domain. Prior-domain completeness and closed-child tree coverage remain bearing premises for exterior exclusion. The FINAL896-vertex-list completeness is now unnecessary for box entry: C1371 gives20 exact rational linear-dual inequalities directly from halfspaces, with all approximate-dual residuals bounded on the simplex.
5. C1370: transport by sites [7,5,1,8,0,4,6,2,9,3,13,11,12,10], anchors j→j+2 mod10. Exact mean-gauged angle bounds put the WHOLE domain inside |delta|inf<.004245. An explicitly balanced damped affine flow yields a uniform quadratic minorant on |delta|inf<=.005. Gap-cap cancellation and directed arithmetic give ||delta||2²<1.265464e-14, thus ||delta||inf<1e-6. Exact reference-anchor comparison adds <2e-14; hence the full 16-face witness system enters C1355's 2e-6-radian anchor cell after ONE common rotation.
6. C1355 then supplies the gauged C1262 site-box interface and excludes r<r*. C1281's once-winding Cartesian witness coverage implication is retained; the 40-edge flow core alone is NOT the input of the local theorem.
7. The preceding interfaces give a contradiction for every arbitrary cover at r<r*. Together with C1167's exact attainment, this proves the unrestricted optimum. No uniqueness claim about the original, unnormalized centers is inferred here.

## Current proof level
C1370 is registered proved-interval with an independent analytic review of the new flow/box/cap/norm-domination bridge. Producer fixed-dyadic and independent directed-Fraction implementations check the matrix inequalities; independent direct-prefix angle reconstruction checks domain-to-box transport. These are not independent validation of every inherited topology, root, or local AD premise.

Final inherited-interface audit is closed. The root report `members/root-cc2/final-local-interface/REPORT.md` corrects its initial pre-/post-gauge substitution and reproduces first-exit ratio .84578364474801238<1 with exact Fractions. The topology report `members/topology-audit-cc2/final-interface/REPORT.md` retracts its false six-unverified-cuts objection after inspecting the actual automorphism loop. Lead `q10_cut_transport_provenance.py/.json` independently verifies four16-face/10-owner-pair automorphisms, exact deficit transport, every round2..8 tree's structural coverage and transported cut set. `q10_domain_row_provenance.py/.json` checks every halfspace insertion from the tight-domain root through C1366. These new checks supplement, not replace, the earlier complete-root enumerations, inductive rational clipping, and independent directed leaf-bound replays.

The lead also inspected the analytic connected-owner/outward-clip/finite-graph-limit reduction, complete catalogue enumeration argument, complete root-support enumeration, exact clipping criterion, concave leaf minorant and its Fraction implementation, exact KKT rank argument, full mixed directional AD Hessian enclosure, and first-exit growth implication. No reviewer label or source hash is used as a mathematical premise.

C1371 was independently replayed and analytically reviewed in `members/stress-cc2/halfspace-dual-audit/REPORT.md`; shared L/pi constants retain their exact alternating-arctangent and positive-asin-series enclosures, not the report's merely numerical mpmath check. Each retained interface now has the required domain/normalization and rigorous implication. There is no remaining mathematical implication in this assembled chain.

Source snapshot: `q10-final-bridge-manifest.json`; hashes are integrity checks, not mathematical proof. Registry reachability: `final-claim-dependency-check.json`; no missing or retracted listed dependency, but registry status does not certify truth.

## Original-success-criteria check
- Exact value: locally unique algebraic root in the explicit rational isolating box, not a rounded decimal or claimed globally unique root.
- Attainment: fourteen explicitly defined centers cover the ENTIRE closed unit disk (boundary plus complete interior nearest-maxima check).
- Unrestricted lower bound: every arbitrary14-center cover at any smaller radius is carried through necessary reductions and excluded; no symmetry, general position, or prescribed contact graph assumed initially.
- Degeneracies: projection/merging and outward clipping with compact limits are retained; closed tree children include split interfaces.
- Scope not claimed: uniqueness of original unnormalized centers, a short elementary proof, machine-checked proof-assistant formalization, or publication/novelty priority.

Next action beyond the completed theorem: package a standalone manuscript and immutable certificate bundle for external reproduction; this is dissemination/verification, not an unproved mathematical bridge.
