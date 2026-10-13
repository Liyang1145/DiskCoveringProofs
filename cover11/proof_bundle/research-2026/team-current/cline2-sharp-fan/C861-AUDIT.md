# C861-AUDIT.md — audit of HIGH-BEARING-BOUNDARY-THEOREM.md / certify_hub_laplacian.py

Owner: cline2-sharp-fan (own files only; no kernel write, no grids).  Independent checks in
tools/hub_disk_audit.py + ad-hoc mpmath runs; key numbers reproduced below.

Domain audited: r in [3/8, 19/50], b1,b2 in [1, acos(r)] (so 1 <= bj <= 1.187, i.e. high bearings),
s = sqrt(1-r^2), Delta = delta = b1 - A = B - b2, and the C848 lens
Omega = (3 disks) INTERSECT (wedge A >= 0, B >= 0) in the (v,t) chart.

VERDICT: the reduction is CORRECT on this domain.  Every ingredient checks out; two presentation
points are worth recording so the wedge branch cannot be misread.

================================================================================
1. THE LAPLACIAN IDENTITY — EXACT, CONFIRMED
================================================================================
F(v,t) = affine(v,t) + a1 theta1 + a2 theta2 + beta1 L1^2 + gamma1 L1 + beta2 L2^2 + gamma2 L2,
theta_j = atan2(Y_j, X_j), L_j = |(X_j,Y_j)|, (X_j,Y_j) = (v,t) - Q_j up to a reflection.
 * Delta(affine) = 0; Delta(theta_j) = 0 because theta_j is the polar angle of an AFFINE map whose
   linear part is orthogonal (a reflection composed with a translation) — so each angle term is
   HARMONIC in (v,t), not merely small;
 * Delta(beta_j L_j^2) = 4 beta_j (Delta |x|^2 = 4);
 * Delta(gamma_j L_j) = gamma_j / L_j (Delta |x| = 1/|x| in 2D, away from Q_j).
Hence ** Delta F = 4(beta1 + beta2) - c1/L1 - c2/L2 with c_j = |gamma_j| = 1.145102454, 1.138494697 **.
Checked numerically by a second-difference Laplacian at h = 1e-6, dps = 30: at
(r,b1,b2,v,t) = (.3795,1.07,1.05,.42,-.18) numeric 1.26444131789 vs formula 1.26444131788, and at
(.375,1.10,1.09,.40,-.10) numeric 1.66816187114 vs formula 1.66816187114.  Exact identity, 11 digits.

================================================================================
2. THE RECIPROCAL CAP — CORRECT, WITH THE VERTEX ARGUMENT MADE EXPLICIT
================================================================================
The two inputs:
 (i)  L_j <= 2r for j = 1,2;
 (ii) L1 + L2 >= d := |c1 c3| >= 4 r sin^2(1).
 (ii) derivation: D_j = 2r sin b_j >= 2r sin 1 (b_j >= 1), and
      d^2 = D1^2 + D2^2 - 2 D1 D2 cos(b1+b2) = (D1-D2)^2 + 2 D1 D2 (1 - cos(b1+b2));
      b1+b2 >= 2 and cos decreasing on [2,pi] give 1 - cos(b1+b2) >= 1 - cos 2 = 2 sin^2 1, so
      d^2 >= 0 + 2 (2r sin1)^2 (2 sin^2 1) = 16 r^2 sin^4(1), i.e. d >= 4 r sin^2 1.  (Verified:
      4r sin^2 1 = 2r(1 - cos 2) = 1.062110127 at r = 3/8.)
Cap: (L1,L2) -> c1/L1 + c2/L2 is convex on the polygon {L_j <= 2r, L1+L2 >= d} (d <= 4r), so its
maximum is at a vertex; the vertices give (c1+c2)/(2r), (c1/a + c2)/(2r) and (c1 + c2/a)/(2r) with
a = -cos 2 = 0.416146836547, the first being dominated, so
    c1/L1 + c2/L2 <= max( c1/a + c2, c1 + c2/a ) / (2r).
Observed values: (c1/a + c2)/(2r) = 5.186898 at r = 3/8 (the larger case), (c1+c2/a)/(2r) = 5.174537,
(c1+c2)/(2r) = 3.0047.  Since the cap scales like 1/r while 4(beta1+beta2) = 5.583507299 is
r-independent, the worst case is the SMALLEST r:
    ** Delta F >= 5.583507299 - 5.186898080 = 0.396609219 > 0.3966 **   (r = 3/8).
So F is strictly SUBHARMONIC on Omega: no interior local maximum is possible, hence the maximum is
attained on the boundary.  (Note this uses L_j <= 2r, not the sharper face form.)

================================================================================
3. WEDGE / ANGLE BRANCH — audited closely, and it HOLDS (here is the clean form)
================================================================================
The face constraint is not merely "L_j <= 2r"; it is exactly
    ** L_j <= 2 r sin(thC_j),   thC_1 = A = b1 - Delta,  thC_2 = B = b2 + Delta **
because the C848 face quadratic equals L_j^2 - 4 r^2 sin^2(thC_j) (from L_j^2 = H^2 + D_j^2 -
2 H D_j cos(thC_j) and the quadratic's form H^2 + D_j^2 - 2 H D_j cos thC_j - 4r^2 sin^2 thC_j).
On the wedge edge A = 0 this forces L1 = 0, i.e. the hub coincides with c1; and the hub-norm disk
|(v,t) - (s,0)| <= 1 - r excludes c_j, since (in the (v,t) chart the ring centre c1 is the point
(D1 cos b1, D1 sin b1))
    |c1 - (s,0)|^2 - (1-r)^2 = 2r [ (1-r) + 2r sin^2 b1 - 2 s sin b1 cos b1 ].
On the domain the bracket is strictly positive and in fact bounded away from 0: the left part is
>= (1-.38) + 2(.375) sin^2 1 = 1.151 while the right part is <= 2(.9271) max(sin b1 cos b1) =
2(.9271)(0.4546) = 0.843 (using sin b1 cos b1 = 0.5 sin 2b1 and 2b1 in [2, 2.374]).  So c_j lies
strictly outside the disk with margin of order 0.3 in the squared distance.  Same for B = 0 and c3.
Consequence: the wedge edges meet Omega in the EMPTY set, Omega is the compact set
(3 closed disks) INTERSECT (closed wedge), its boundary is contained in the union of the three
circles, and the maximum of F lies on those arcs.  Because the wedge boundary is excluded and the
ring centres are excluded, Omega stays at distance > 0 from each Q_j, so L_j >= lambda_j > 0 on the
closure and F is C^2 there — no singularity enters the maximum-principle argument.

================================================================================
4. PRESENTATION POINTS (not errors)
================================================================================
(P1) Keep the two face forms apart: L_j <= 2r is what powers the reciprocal cap; L_j <= 2r sin thC_j
     is what kills the wedge edges.  The note's line "Lj <= u = 2r" and its wedge sentence are both
     right, but the wedge step does not follow from L_j <= 2r alone.
(P2) The constant a = -cos 2 comes from b1+b2 >= 2; the hypotheses b_j >= 1 is therefore essential,
     exactly as the note says, and the reduction is a high-bearing statement only.
(P3) Domain interfaces checked: b_j <= acos(r) (legality, not used by the bound), the hub-norm
     identity |c9| <= 1-r <=> (v-s)^2 + t^2 <= (1-r)^2 (Round 18), and r in [3/8, 19/50] enters only
     through the 1/r scaling of the cap and through D_j >= 2r sin 1.
(P4) Nothing here assumes the ridge maximizes anything, and no objective concavity is used: the
     statement is "interior eliminated, maximum on the three disk arcs" — a 2D-to-1D reduction on
     this box.

STATUS: audit complete; reduction confirmed; no claim registered, no kernel write, no grids rerun.
