# Effective interpolation bridge for q10/879

Route: generic, **unverified**. Read STATUS.md and DEAD.md before exploration. One analytic route and a finite scalar/certificate diagnostic; no optimization or grid. All new writes are in this directory. No lead certificates or partial strip trees were modified.

## Result / scope

**Analytic consequence of C1167, C1262 and C1281, with rational checks on the saved C1262 enclosure:** if the ten literal q10/879 anchors differ from the exact candidate by at most **2e-6 radians after ONE common rotation**, every feasible Cartesian witness system of radius r<=U=.33173203427623414 has its sites, after the X+ gauge, within **5.27e-8 in full 28-dimensional Euclidean norm** of the exact candidate. In particular no such system has r<r*, and at r=r* its sites equal the candidate. No witness uniqueness is asserted.

This gives an effective bridge beyond the previously recorded 1e-6 cell, without a grounded-flow premise. **It does not outperform the existing dual method on cell size:** an unchanged-formula, redirected copy of the lead dual certificate also certifies the 2e-6 cell, with gauged site error 2.764e-5<4e-5. Combining that membership with the penalty estimate below also gives the stronger 5.27e-8 site error. Thus the new structural content is a quantitative convex-interpolation/first-exit mechanism and an extracted growth constant, not evidence that interpolation is the superior localization instrument.

The unrestricted optimum and the exterior of this tiny cell remain open. No claim that C1350 lies in this cell; no global exclusion or anisotropic region outperforming dual slack has been obtained.

## 1. Exact objects and inherited dependencies

Use the literal site order of `lead/local_sosc_certificate.py` and `dual_slack_localization_certificate.py`: X+=site9=(s,0), s=sqrt(1-r*^2). Anchors are

    (s,r*), (px,py), (0,1), (-px,py), (-s,r*),
    (-s,-r*), (-px,-py), (0,-1), (px,-py), (s,-r*).

Site9 is incident to the first and last anchors. The same literal graph is production 10/4[879] through the existing catalogue correspondence; no new index transport is performed here. All 14 sites and all 16 shared face witnesses are retained. Constraints are the 20 anchor-owner and 48 face-site distances <=r. C1281 supplies actual coverage when anchors are ordered on the circle; it does NOT identify a recovered nearest Voronoi type.

Bearing sources inspected: `members/q10-anchor-curvature/REPORT.md` (C1352), `lead/Q10-ANCHOR-GROWTH-AUDIT.md`, `LOCAL-DIRECTIONAL-BOX.md`, `local_neighborhood_directional.py`, `local_sosc_certificate.py`, `DUAL-SLACK-LOCALIZATION.md`, and its certificate script. C1352's qualitative compactness step is replaced here by explicit interpolation and first exit. Exact root existence, nearest contact branches and exact KKT identities remain inherited premises, not independently recertified.

## 2. Effective squared-radius growth from the saved penalty

Let eps=1/25000. In the X+ gauge, C1262 proves on the entire coordinate box |C-C*|_infty<=eps that

    P(C)=sum_(18 positive contacts) [lambda_k delta_k + (3/2)delta_k^2],
    delta_k=f_k(C)-r*^2,

has P(C*)=0, gradient zero and W^T Hess(P) W >=(1-b) I, with the exact saved b<1. The gauge penalty is zero on this gauge; its Hessian is included in that matrix bound. The contact multipliers sum to **one**, as checked in source normalization, not eighteen.

From the exact rational W, bound ||W||_2^2 by the minimum of its Frobenius square and the maximum absolute row sum of W^T W. The latter gives B<72.937436. Therefore

    Hess(P) >= mu I,  mu=(1-b)/B > .00857761.

For a cover in this box put h=r^2-r*^2. If h<0, the original penalty-sign proof already forbids the cover. For 0<=h<=h0=1/1000, each delta_k<=h. For negative delta_k the certified sign 2lambda_k+3delta_k>0 implies its penalty term <=0; for positive delta_k its term <=lambda_k h+(3/2)h^2. Thus

    (mu/2)||C-C*||_2^2 <= P(C) <= h+27h^2,
    h >= kappa ||C-C*||_2^2,                       (G)
    kappa = mu/[2(1+27h0)] > .00417605.

This argument **does not assume** lambda_k+3delta_k>0 on the whole box; C1262 saved the weaker sign and it suffices by splitting negative/positive delta. The same bound rules out h<0 and forces C=C* when h=0.

`diagnostic.py` recomputes b from every saved rational matrix interval and extracts B, mu, kappa exactly. This is a new rational implication of the saved enclosure, not an independent AD or KKT certificate.

## 3. Joint Cartesian interpolation and radial repair

Start with a feasible endpoint (C,w,A,r), and exact (C*,w*,A*,r*). Rotate the ENTIRE endpoint system together into a chosen gauge first. Choose one consistent lifted anchor branch and write A_j=exp(i(theta_j*+a_j)), beta=max_j|a_j|<pi. Interpolate ALL free variables and anchors in Cartesian coordinates:

    C_t=(1-t)C*+tC, w_t=(1-t)w*+tw,
    B_j(t)=(1-t)A_j*+tA_j, r_t^lin=(1-t)r*+tr.

Convexity makes every original incidence distance <=r_t^lin. Set Ahat_j=B_j/|B_j| and

    q_j(t)=|B_j(t)|=sqrt(1-2t(1-t)(1-cos a_j)),
    e_j(t)=|Ahat_j-B_j|=1-q_j(t), e(t)=max_j e_j(t).

Increasing radius to rhat_t=r_t^lin+e(t) repairs all anchor inequalities; interior constraints need no repair. For beta<pi,

    e(t) <= t(1-t) beta^2/[2 cos(beta/2)].             (R)

Proof: 1-q=2t(1-t)(1-cos a)/(1+q), q>=cos(beta/2), and 1+q>=2cos(beta/2). The exact e(t) is preferable when available. At t=0,1 or a_j=0 the repair is zero. At an antipodal midpoint q=0 and normalization is invalid; that degeneration is explicitly excluded, not ignored.

**Order is a separate obligation.** For |a_j|<pi, the normalized chord lies on the short arc between its endpoints. In our cell all repaired angle displacements therefore have absolute value <=beta. The reference adjacent gaps are in (.1,pi/2), verified from interval cross products >.1 and dot products >0, with once-winding order inherited from the exact construction. beta<=.001 then preserves positive gaps <pi and the single lifted winding throughout interpolation. Merely assuming both endpoint polygons are ordered would not justify this assertion for arbitrary large motions.

The repaired system consequently gives an actual cover by C1281. No embedding, face orientation or nearest-type hypothesis is added.

## 4. The effective first-exit inequality

First suppose the endpoint is in the **X+ gauge with x_9>0**, and |a_j|<=beta<=.001 in that same gauge. Then the straight center segment stays in that gauge. Let D=||C-C*||_2. For tD<=eps it lies inside the C1262 box. Let eta=U-r*; do not replace U by r*.

By (R), for a=1/[2(1-(.001)^2/8)] (using cos x>=1-x^2/2),

    rhat_t-r* <= t eta + a t(1-t) beta^2.

Whenever the right side is nonnegative, its magnitude is tiny in the stated beta range; the root interval verifies

    h_t=rhat_t^2-r*^2 <= .665 [t eta+a t(1-t) beta^2] <h0.

If h_t were negative, C1262 would already contradict existence. Combining with (G) gives the principal inequality

    kappa t^2 D^2 <= .665 [t eta+a t(1-t) beta^2].     (I)

For D>=eps choose t=eps/D, the first exit from the Euclidean eps-ball, which is contained in the coordinate box. Divide by t:

    kappa eps D <= .665 [eta+a(1-eps/D) beta^2]
                    <= .665 [eta+a beta^2].          (E)

Thus the explicit sufficient entry criterion is

    .665 [eta+a beta^2] < kappa eps^2.                (ENTRY)

It forces D<eps for **every** feasible endpoint, not just an optimizer. Then apply (G) directly at the endpoint:

    ||C-C*||_2^2 <= (U^2-r*^2)/kappa.                 (FINAL)

This also proves radius>=r*, with equality only at the candidate sites. At U the small positive excess cannot be discarded; (FINAL) is closeness, not equality.

For an arbitrary initial gauge, one can instead align centers by Procrustes. This gives d_rot(C_t,C*)=t d_rot(C,C*) exactly, because the endpoint correlation with C* is real nonnegative. A final X+ alignment increases per-site error by at most K=1+2/.9=29/9 as long as tD is small. Replacing eps by tau=eps/K yields a conservative orbit-distance version of (E). **The beta in that formula must be measured after that same center alignment**, not after a separately optimized anchor rotation. The scalar table in diagnostic.json concerns this conservative joint-gauge version; it is not by itself an anchor-only theorem.

## 5. Anchor-only gauge control and the 2e-6 cell

Now assume anchors are within epsilon_A=2e-6 of A* after one common rotation; sites are arbitrary. Use the two anchors of X+. Let X+=(x,y), u=x-s. Anchor displacement in Euclidean norm is <=epsilon_A, so both distances to the exact reference endpoints (s,+/-r*) are <=U+epsilon_A. Adding their inequalities gives

    u^2+y^2 <= H,   H=(U+epsilon_A)^2-r*^2.

Taking their maximum gives the sharper tangential bound

    u^2+y^2+2r*|y| <= H,
    |y| <= H/(2r*), x>=s-sqrt(H)>0.

Hence the rotation alpha taking X+ to the positive x-axis obeys

    |alpha| <= |y|/x <= H/[2r*(s-sqrt(H))].

Use root-interval lower bounds for s,r* and an upper bound for H to make every quantity rigorous. After rotating the whole endpoint system, its anchor displacements satisfy

    beta <= epsilon_A + H/[2r*(s-sqrt(H))].

The finite rational/interval diagnostic verifies beta<.001 and, with this beta,

    .665(eta+a beta^2)/(kappa eps^2) < .846 <1.

Thus (ENTRY) holds on the complete 2e-6 anchor box, not merely samples. Finally the root interval gives

    sqrt((U^2-r*^2)/kappa) < 5.27e-8.

This lens estimate is essential: a naive angular gauge estimate O(sqrt(epsilon_A)) would destroy the gain. The two almost diametral endpoints force the tangential component to be O(epsilon_A), while the radial component can be O(sqrt(epsilon_A)). The sites need not be normalized boundary owners; the original incidence constraints suffice.

## 6. Comparison with grounded-flow dual slack / precise limitation

The existing flow method bounds weighted edge errors directly by its slack and localizes sites through positive-support resistances. It has no small-t loss. The inspected source uses 44 positive edges, approximate alignment with an explicit residual, path grounding and a gauge correction. No exact alignment is assumed here either.

`dual_comparison.py` is the existing lead script with only an import-path prefix and output redirected into this directory. At epsilon_A=2e-6 it returns **2.7633839311e-5** gauged error, already below 4e-5. This is a same-kernel/source comparison, NOT an independent implementation. Consequently the effective cell increase is real relative to the saved 1e-6 claim, but it is **not a superiority result** for the proposed interpolation route. The much tighter 5.27e-8 final norm follows once *either* method enters the local box and applies (G).

The obstruction to a large bridge is visible in (I): repaired radius is O(t beta^2), whereas local growth is O(t^2 D^2). Sending t to zero loses rather than strengthens control. First exit leaves D <= O(beta^2/eps), or an entry requirement beta^2=O(kappa eps^2). The conservative constant is kappa~.00418 and eps=4e-5, so the usable beta is only a few microradians. This is not a disproof of better direction-sensitive estimates, but it gives no route to the current much wider global metric region.

A materially larger anisotropic bridge needs a stronger, explicitly verified inequality, e.g. a direction-dependent repair bound and penalty form satisfying at first exit

    (1/2)(1-b)||W^{-1}(C_t-C*)||^2
        > h_t+27h_t^2

for every forbidden endpoint direction, with the common gauge and whole legal anchor domain controlled. The present max-angle repair and scalar kappa do not establish that inequality outside the stated cell. A derivative at the candidate or a sampled value Hessian cannot replace it.

## Evidence / reproduction / one next action

Run from workspace root:

    py -3 -B research-2026/next-cover-global/members/q10-effective-localization/diagnostic.py
    py -3 -B research-2026/next-cover-global/members/q10-effective-localization/dual_comparison.py 1/500000

Outputs: `diagnostic.json` (source hashes, exact rational constants/entry comparisons and finite scalar table), `dual-comparison-2e6.json`. The diagnostic imports only the read-only root arithmetic kernel (main guard inspected), calibrates it, and reconstructs the exact root-box geometry. It does not import the side-effecting local SOSC producer or run any lead writers. Saved C1262 geometric enclosures and exact KKT remain bearing dependencies.

**One next action:** have the lead audit this explicit penalty-growth/first-exit implication and, if accepted, use a 2e-6 cell handoff (either localization route suffices) without altering partial trees. Further global work still requires exterior exclusion; no promise of a larger anisotropic certificate is made.
