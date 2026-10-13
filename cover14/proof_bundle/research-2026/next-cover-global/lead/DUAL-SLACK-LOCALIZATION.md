# Dual slack localizes the eliminated Cartesian variables

Scope: fixed incidence graph of the C1281 witness SOCP, with free points x, fixed circle anchors A, radius r>0. Orient p_e=x_tail−x_head (free tail, free or anchor head). Any nonzero exactly balanced vector flow z has weights lambda_e=||z_e|| and unit directions u_e=z_e/lambda_e on positive-weight edges. Let N=sum lambda_e and L_z(A)=sum z_e·p_e, independent of x by balance.

For every feasible system ||p_e||<=r:

    sum_e lambda_e ||p_e−r u_e||² <= 2r (rN−L_z(A)).                 (1)

Indeed expand each squared norm and use ||p_e||²<=r². This is a full vector estimate, not coordinatewise curvature or a numerical stationarity assertion. Zero-flow edges contribute nothing. The right side is nonnegative by the usual flow lower bound.

Let reference data (x*,A*,r*) be feasible and let p*_e its incidence differences. Suppose the positive-weight flow directions align exactly on every positive-weight edge: p*_e=r* u_e. Write rho=r/r*, y=x−rho x*, b=A−rho A*. Then (1) becomes

    E(y,b)=sum lambda_e ||y_tail−y_head||² <= 2r(rN−L_z(A)),        (2)

where fixed heads have value b. Thus there is no need to infer free-variable closeness from anchors alone: the missing quantity is the **dual slack**.

For a path P_v of positive-weight incidence edges from free vertex v to anchor a, weighted Cauchy–Schwarz gives

    ||y_v−b_a|| <= sqrt(R_v E),   R_v=sum_(e in P_v) 1/lambda_e.

Consequently

    ||x_v−x*_v|| <= ||A_a−A*_a||
       + |rho−1| ||x*_v−A*_a|| + sqrt(2r R_v (rN−L_z(A))).        (3)

Every positive-weight component must touch an anchor to localize all free points. Connectedness of the UNWEIGHTED incidence graph does not establish this; verify the positive support explicitly. Weighted grounded Laplacian inverse/resistance can improve the path bound but is not needed for validity. Sites, not witnesses, are the inputs to C1262's local box; the final estimate must use the same label map and rotation gauge.

If alignment is only approximate, use sqrt(E) <= sqrt(2r(rN−L_z(A))) + (r/r*) sqrt(sum lambda_e ||p*_e−r* u_e||²), by the weighted Euclidean triangle inequality. This version accommodates an exact rational repaired flow with a certified reference residual. Approximate alignment must NOT be silently treated as exact.

For any r<=U, a certified anchor-cell lower Lmin gives rN−L_z(A)<=UN−Lmin. Also need a lower radius bound r>=rlo>0 if bounding |rho−1|, and interval bounds for reference coordinates and flow norms. Thus a box near candidate anchors plus tiny certified slack can imply all site centers lie in C1262's exact local box. This would close the inner-variable interface of a future global-to-local branch proof. The quantitative bridge below now certifies a local anchor cell; the square-root slack budget is stringent (roughly epsilon² after resistances).

## Historical first support diagnostic (numeric only; superseded)
The saved single SOCP-dual proposal is sparse:32/68positiveedges and sites4,5,8,9 are not connected to anchors in its positive support (`dual-slack-localization-probe.json`). Thus it does NOT satisfy the localization premise. This is not an impossibility result: averaging the flow over exactD2 graph/anchor symmetries preserves balance and sharpness at reference, may fill missingC-site support. The two Xsites additionally have diametral anchorpairs separated by2r*, supplying elementary opposite-pair sharp flows. A positive convex combination of these with symmetry-averaged mainflow is a candidate grounded sharp flow. Requires exact alignment/balance and support verification; not yet constructed.

## Certified local anchor cell
`dual_slack_symmetric_flow.py/json` constructs an exactly balanced rational flow by averaging the prior flow under literal graph reflections and adding opposite vertical flows at the two X sites. Forty-four edges are positive and all 14 sites are grounded. No exact alignment is assumed. `dual_slack_localization_certificate.py/json` reconstructs the complete site–witness/anchor incidence and uses the C1167 root interval to enclose the reference alignment residual.

For the literal face/owner labeling, assume after one common rotation that each anchor angle differs from its exact reference angle by at most ε=10^−6 radians. Put g_j=−sum of anchor-incidence flows, F0=Σg_j·A*_j, T=Σ|g_j·J A*_j|, G=Σ||g_j||. Taylor's theorem (unit reference anchors) yields L(A)≥Lmin=F0−Tε−Gε²/2. With rlo=Lmin/N>0, feasibility implies rlo≤r≤U. The certificate bounds |r/r*−1|, the reference residual, and positive-path resistance separately, without assuming r≥r*.

The resulting Euclidean error per site is <4.606×10^−6. For X+=site9=(s,0), s>0.943, an additional rotation to y(X+)=0 has magnitude ≤2 error/s (error<s/4 checked). It raises the per-site error to <1.382×10^−5, strictly within C1262's 4×10^−5 coordinate box. Thus the local necessary witness system plus this anchor-cell hypothesis feeds C1262 for an **actual covering** at r≤r*: there is no strictly smaller covering within this cell. The bridge itself does not assert every abstract feasible witness system is an actual cover.

Independent analytic interface audit: `../members/dirichlet-cut-audit-cc2/SLACK-LOCALIZATION-AUDIT.md`; independent high-precision numbers are corroboration, not a second interval certificate. One report note incorrectly called N/F0 point upper values: the actual JSON stores two-sided intervals of widths about6.41e−70 and1.26e−19; only `slack_upper` is explicitly collapsed to an upper point.

Remaining global obligations: exclude all other anchor cells for q10/879 and the still-unaudited q11 families. This lemma alone does not remove a whole catalogue family.
