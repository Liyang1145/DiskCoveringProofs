# q10/879: local quadratic growth transfers to the anchor SOCP

Route: independent analytic reasoning; underlying model route unverified. Read STATUS.md and DEAD.md first. All new writes are in this directory. This is one analytic route, with one finite endpoint-sign interval check, not a numerical curvature survey.

## Result in one paragraph

**Analytic consequence of C1182/C1262, C1167 and C1281:** the fixed-anchor witness value V_879 has **local quadratic growth at the exact candidate, modulo common rotation**, on the full ordered-anchor neighborhood (hence also on its capped-gap domain or saturated-gap strata). No symmetry of perturbations is assumed. This does **not** establish local strong convexity, a differentiable value Hessian, an effective neighborhood larger than C1324's 1e-6 cell, or exclusion of the rest of C1350. The proof transfers the already certified actual-center SOSC through convexity of the fixed-anchor fiber and transverse endpoint inequalities. It avoids parametric SOCP differentiability entirely. A fixed sharp Dirichlet stress cannot provide this quadratic growth: C1175's descent is already arbitrarily local.

## 1. Exact objects and bearing inputs

Let K be production `lead/k10-catalogue-corrected.json`, `10/4[879]`, identified with the literal candidate by the existing exact graph correspondence. Let theta* be its exact C1167 anchor angles on one lifted ordered branch. V(theta) is the minimum r over all **14 shared sites and all 16 shared face witnesses**, subject to the 20 anchor-owner and 48 face-site distance inequalities <=r. Anchors are exp(i theta_j); successive gaps are in (0,pi), and the lifted cycle winds once. All these strict gap conditions hold near theta*.

Use

    d_rot(theta,theta*) = min_alpha ||theta-theta*-alpha 1||_2

on this one local lifted branch. The common-angle shift is rotation only, not a symmetry WLOG. The radius is r*, the exact C1167 root, not the decimal upper bound U.

Bearing facts used, not independently recertified here:

* C1167: exact candidate feasibility and contacts (`lead/ROOT-ATTAINMENT.md`).
* C1182/C1262: actual-center local SOSC and full mixed positivity modulo rotation (`lead/LOCAL-SOSC-PROOF.md`, `LOCAL-DIRECTIONAL-BOX.md`).
* C1281: **these Cartesian witness inequalities imply an actual cover**, even with inverted/degenerate interior drawings, provided the ordered anchor boundary conditions hold (`lead/DEGREE-COVER-WITHOUT-EMBEDDING.md`, `FIXED-ANCHOR-CONVEX-REDUCTION.md`). This is sufficiency for a cover, NOT equality with the fixed extracted Voronoi type.
* The fixed-anchor feasible fiber is convex and attained; uniformly bounded sublevel fibers follow by incidence paths to anchors.

Important interface correction: C1335's elimination is indeed an IFF only for the incidence system, and gives no nearest/empty-circle identification. But its statements that incidence feasibility does not imply coverage must not be used to discard C1281: after imposing the ordered unit-circle anchor hypotheses, the *full* Cartesian incidence system does imply coverage by the established PL-degree theorem. No additional embedding assertion is needed. Without those anchor hypotheses, the caution is valid.

## 2. Transfer theorem

**Proposition.** There exist epsilon>0 and c>0 such that, for every lifted ordered theta with d_rot(theta,theta*)<epsilon,

    V(theta) >= r* + c d_rot(theta,theta*)^2.                  (T)

This includes nonsymmetric perturbations and does not assume the two maximum gaps stay saturated. Constants in (T) are existential here; no membership of all C1350 is claimed.

### Step A. Actual-center SOSC gives quadratic growth, not merely strictness

Write C in the C1182 local rotation gauge, v=C-C*, R=r^2, and R*=r*^2. There are a neighborhood and kappa>0 such that every cover in this neighborhood satisfies

    R-R* >= kappa ||v||_2^2.                                 (A)

Here is the short consequence of the existing SOSC proof. If (A) failed, local strict optimality would give covers C_n!=C* approaching C*, with 0<=h_n=R_n-R*=o(||v_n||^2). Take v_n/||v_n|| -> u. First-order feasibility of the 24 smooth necessary contacts gives grad f_k.u<=0. Exact KKT implies every positive-multiplier contact has grad f_k.u=0; the gauge also vanishes. Thus u is a nonzero critical direction. Weighted second-order feasibility and exact stationarity give

    h_n >= (1/2) v_n^T H v_n + o(||v_n||^2).

The existing **full mixed** SOSC is positive on u, contradiction. This uses the actual analytic KKT identities and certified quadratic form, not an approximate multiplier fit.

Alternatively C1262's uniformly positive Hessian of P gives an effective center constant after shrinking so each scalar penalized-contact term is increasing. The current report does not implement that quantitative refinement.

### Step B. Every optimum at the exact anchors has the candidate sites

Suppose (C',w',r') is feasible at theta*, with r'<=r*. Interpolate it linearly with the exact candidate witness system. The SOCP constraints remain feasible at the interpolated radius <=r*. By C1281 each interpolation is an actual cover. For sufficiently small positive interpolation parameter, C1262 forces its centers to be a common rotation of C* and its radius to be r*.

This implies C'=C*: the polynomial ||C*+t(C'-C*)||_F^2 would otherwise have a strictly positive t^2 coefficient, whereas a common rotation preserves this norm and makes it constant on a nonempty interval. Consequently r'=r*. In particular V(theta*)=r*, and **the site part** of every minimizer is unique. The witness part need not be unique and is not asserted to be.

No convexity of the rotation orbit is assumed in this argument; the norm polynomial is the step excluding it.

### Step C. Near-anchor minimizers have near-candidate sites

The value function has the elementary ambient Lipschitz estimate

    |V(A)-V(B)| <= max_j |A_j-B_j|.                            (B)

Indeed keep all free sites/witnesses and increase r by the maximum anchor displacement, then reverse A,B. Attainment justifies using minimizers, though infima suffice for (B).

If theta_n -> theta*, choose any minimizers. Their radii tend to r* by (B), and all their free coordinates are uniformly bounded by finite incidence paths. Any convergent subsequence therefore limits to a feasible optimizer at theta*. Step B forces its sites to C*. Hence **all** near-anchor minimizing site arrays approach C*, regardless of possible witness nonuniqueness. They can be put into the small C1182 X+ gauge. This is a compactness argument, not quantitative localization and not a claim that the entire feasible fiber near theta* is close at arbitrary radii.

### Step D. Anchor motion is controlled by site motion and excess radius

At anchor j, the preceding owner's boundary-distance function has strictly positive angular derivative and the following owner's has strictly negative derivative:

    q_i(t,C_i)=|exp(it)-C_i|^2,
    partial_t q_i = 2(C_ix sin t-C_iy cos t).

At the exact contacts, q_i(theta_j*,C_i*)=R*. The finite interval check below proves all twenty signed derivatives exceed **1/5**. Thus, after shrinking the angle neighborhood, they retain magnitude at least some m>0 (e.g. 1/10).

Rotate a minimizing system into the center gauge and write a_j for its resulting anchor-angle displacement, v for its site displacement, and h=V(theta)^2-R*. For a_j>=0 use the preceding owner; for a_j<=0 use the following owner. The mean value theorem at the *fixed reference site*, followed by the locally Lipschitz site dependence of q, gives

    m |a_j| <= h + B ||v||_2.                                 (C)

All constants are uniform on a sufficiently small neighborhood. Both endpoint inequalities are needed: mere transversality of the equidistance switch would not alone prove (C).

By Steps A-C, h>=kappa ||v||^2>=0. Squaring and summing (C), then shrinking to h<=h0, gives

    ||a||_2^2 <= (20/m^2)(h^2+B^2||v||^2)
              <= (20/m^2)(h0+B^2/kappa) h.

Since d_rot<=||a||, and h=(V+r*)(V-r*) with V+r* uniformly bounded, this proves (T). The possible small rotation used for the center gauge is harmless: it is exactly the common shift allowed in d_rot.

This proof neither differentiates an optimizer nor invokes strict complementarity. In particular it survives saturated owner gaps.

## 3. Why a simple stress or an unqualified Schur inverse misses this

C1175's obstruction is already local. Its explicit central descent path keeps both cap-active gaps fixed and allows arbitrarily small positive/negative perturbations, while its free sites **and witnesses** move. Thus any symmetric fixed sharp stress with nonzero central support fails even on the saturated-gap stratum near the candidate. A putative nonsymmetric stress valid on a whole capped neighborhood can be averaged over D2 on the intersection of its four transformed neighborhoods, so the existing obstruction applies there too. This averaging is a proof about a certificate class, not symmetry WLOG for configurations.

There is one crucial distinction: on the stratum where both gaps equal exactly L*=2 asin r*, a stress supported only on the two X anchor paths gives the constant r*^2 after eliminating those sites. It is a valid **nonstrict baseline**, not a positive quadratic-growth certificate. On the full capped neighborhood even that stress fails, by the one-cap-shrinking path in C1175. Therefore:

* fixed sharp stress on a full capped neighborhood: impossible by the existing proof;
* fixed-stress positive quadratic growth on the fixed-saturated stratum: also impossible;
* adaptive SOCP value quadratic growth: (T) holds and does not contradict either.

The force cascade in `STRESS-SUPPORT-ANALYTIC.md` also forces zero multipliers on six tight faces at the reference. The two slack faces add free witness degeneracy. Consequently one must not invert the raw smooth KKT matrix or assume strict complementarity merely because fixed-anchor primal feasibility is convex. A valid sensitivity/Schur calculation would have to select/eliminate the correct critical faces and justify a generalized derivative or strong regularity. (T) does not require those extra assumptions. Nor does it assert that V is C2 or strongly convex between arbitrary pairs of nearby anchor assignments.

C1335's exact elimination remains useful for global work, but choosing a single finite lens branch and differentiating it would introduce its own active-branch obligation. H10 and H12 must retain the same sites 11 and 13. This report never splits these hubs or drops any face constraints.

## 4. Bounded evidence check

Read `lead/q10_joint_basin_control.py` and the actual output filename `lead/q10-joint-basin-control.json`: four numerical local starts are consistent with the candidate but have no bearing role in (T).

New script: `endpoint_signs.py`; output: `endpoint-signs.json`.

    py -3 -B research-2026/next-cover-global/members/q10-anchor-curvature/endpoint_signs.py

It reconstructs exact root-box intervals and the literal ordered boundary contacts from `ROOT-ATTAINMENT.md` / `root_cover_check.py`, and proves all 20 signed endpoint slopes >1/5. The script runs the lead arithmetic calibration first and records source hashes and exact rational interval endpoints. It reuses the lead directed dyadic kernel: **not an independent arithmetic kernel**, and the root existence premise remains C1167. No optimizer, sampling, curvature finite difference, or free-variable grid is used.

Labels are deliberately explicit: this check uses `root_cover_check.py` site order (X+ is site 8), while C1182's different ordering has X+ at site 9. The proof treats site arrays after the existing finite relabeling; it never indexes SOSC coordinates using the root-cover order. Production saturated gaps are 2,7; literal stress gaps are 4,9. Neither equality is silently transported without the catalogue map.

## Remaining gap / one next action

**Structural gain:** local quadratic growth of the abstract fixed-anchor optimum follows without a new SOCP curvature certificate; strict complementarity is not needed. This removes the *qualitative* local-value-curvature obligation, not the global-to-local metric exclusion.

**Remaining gap:** the argument supplies no effective epsilon known to contain the rational C1350 domain, and no proof that its exterior has V>r*. C1324's certified 1e-6 angle cell is still the effective handoff. The C1350 cuts alone do not satisfy the compactness neighborhood premise quantitatively.

**One next action:** make Step C quantitative using the existing positive-support dual-slack estimate and Step A's certified penalty Hessian, with explicit endpoint slopes from this report, to certify one anisotropic neighborhood outside the current 1e-6 box. Any such expansion must control complete fibers and the common rotation; sampling a value Hessian or assuming one optimizer branch cannot replace it. If that explicit region remains much smaller than C1350, global exterior exclusion is still required.
