# STATUS — cline2-sharp-fan (CORRECTED report; numerical only)

Owner: cline2-sharp-fan. Write scope: this directory only.
Lead has rejected the finite criterion and the structural framing of the previous
version of this file. This version (a) records the errors explicitly, (b) keeps only
what is reproducible numeric output, (c) adds no new claims and no new exploration.

> ROUND-11 (central-patch H-fiber audit) is appended at the END of this file, after the
> errata. Read that section for the current task state. Sections ERRATA / WHAT REMAINS
> below are the record of the earlier rejected finite-criterion round.

CALIBER (unchanged): D = unit closed disk; 11 equal disks of radius R; lengths in units
of the unit-disk radius; angles radians. Object: n11/upper/certified_object.json
(centres = integers / 1e17). Certified R interval:
[0.379983853119838709048518179573429853811597902801556119905385,
 0.379983853119838709048518179573429853811597902801556119905389].

================================================================================
ERRATA — statements in the previous version of this file that are WRONG
================================================================================
E1. FALSE (rejected by Lead; my Section 2). "The covering radius is attained in the
    finite set {switches} u {tips}."
    Root cause: I wrote  min_k |x - c_k|^2 = min_k affine_k(x)  and called it concave.
    It is NOT:  min_k |x-c_k|^2 = |x|^2 + min_k (|c_k|^2 - 2 x.c_k), and |x|^2 is
    convex, so the objective is not concave (with a centre at the origin it is |x|^2,
    which is convex). The "concave => maximiser at an extreme point" step is therefore
    unavailable, and in any case that step does not identify the maximiser.
    Also omitted from the candidate set: the ANTIPODAL points of the boundary and the
    HUB-HUB Voronoi vertices, both of which can be essential.
    STATUS: entire finite criterion REJECTED as stated. The numeric agreement at the
    saved candidate (5.6e-17) was a coincidence of that configuration, not evidence.
    Supporting (already-run) evidence that it does not generalise:
      out/p21_criterion_stress.txt — 400 unconstrained random configurations, worst
        (reference - finite) gap = 8.02e-01.
      out/p22_domain_stress.txt — 120 configurations whose 9 rings DO cover bd D,
        worst gap = 1.88e-01 (typical 0.09-0.19). The criterion fails in the domain too.

E2. WRONG terminology. A switch is the NEAREST-SITE bisector intersection with bd D
    (equivalently the common nearest-site point of two consecutive rings), NOT
    universally the intersection of the two radius-R circles. The construction I used
    (inner crossing of two radius-R circles) is a different point in general.

E3. WRONG reading of "|c| + R >= 1". It means the ring disk DOES reach bd D (it is a
    boundary-reaching disk), NOT that the ring is a strictly interior object. My
    phrasing "rings are strictly interior / not boundary-tangent" was a mislabel;
    what is true is only that the disks reach bd D and that no ring is TANGENT
    (i.e. |c| + R = 1 fails for all nine rings of the candidate).

E4. WRONG saturation inference. At R = 0.38 the candidate is UNSATURATED:
    its covering radius is 0.3799838531... < 0.38. Consequently the rings of the
    candidate are NOT pairwise separated by 2R, and any statement of the form
    "the switches are 2R apart" must be dropped.

E5. WRONG run lengths. I wrote (4,3) for the q0(6,7) class. The correct run lengths
    are (4,5).

E6. The file repo-note-sharp-q0-67.md in this directory is RETRACTED in full
    (its Sections 2, 4 and 5 rest on E1).

================================================================================
WHAT REMAINS — reproducible numeric output only (no claim of proof)
================================================================================
N1. Covering radius of the saved candidate (out/p15_final_ledger.txt,
    out/p19_accounting.txt): 0.37998385311983862 ± 1e-14, by dense polar grid
    (1500x7200) plus local Nelder-Mead refinement. Argmax on bd D.
    Repro: py -3 -B -X utf8 tools/p15_final_ledger.py
    Consequence used in the (now rejected) framing, still a fact: the candidate sits
    essentially AT the certified R, and 0.38 - R_cov = +1.615e-05.

N2. Boundary data of the 9 rings at R = 0.38 (same files): the largest nearest-site
    distance attained on bd D is R to within 1e-14, at the nearest-site bisector
    point of rings 9 and 10; other boundary near-tight points: rings 3/5, 7/1, 1/8,
    8/6, 6/4 (each to ~1e-16 of R), while two of the nine boundary bisector points
    carry slack 2.84e-03.

N3. Hub-side ledger (numerical). Hub 0 (|h0| = 0.149428499): three of its fan-tip
    circumcentres lie at distance R from h0 to <= 4e-17. Hub 2 (|h2| = 0.272977466):
    four of its fan tips lie at R to <= 8e-17, and the MEC of its assigned tips is
    0.3785427692 = R - 1.44e-3. Both hubs satisfy |h| + R < 1.
    Caveat from E1/E2: "fan tip" here is the circumcentre of (hub, ring_i, ring_j);
    the identification of such points as the metric critical set is what was rejected.

N4. No-improvement evidence (numeric, finite search; NOT a proof of optimality):
    one-sided perturbations of each of the 22 parameters (step 1e-4..2e-3) and 480
    random product perturbations (scales 1e-4..1e-2) did not decrease the covering
    radius. Files: out/p16_two_conditions.txt, out/p17_minimisation.txt,
    out/p7_local_opt.txt.

N5. Tooling error found and fixed (kept as a reusable guard): certified_object.json
    stores centres as integers / 1e17; integer division silently produced a wrong
    centre set. Tools now divide as int(a)/1e17 and verify reconstruction by
    bisector distance (1.2e-16).

N6. Known complete finite candidate list: cite C529 (Lead's own registration) for the
    complete set of metric candidates of a covering; do not use the set S of E1.

================================================================================
OPEN (unchanged, no progress claimed)
================================================================================
Sharp q0(6,7) remains open: no configuration class exclusion is obtained here, and no
lower bound is improved. Nothing in this directory should be cited as a reduction,
a certificate, or as support for the sharp value.

================================================================================
ROUND 11 — CENTRAL-PATCH H-FIBER AUDIT (own files only)
================================================================================
Task: audit lead/DEGENERATE-SECTOR-HUB-PATCH.md (exact face-circumradius roots +
hub coordinate) and make the feasible H-fiber explicit.
Deliverable: H-FIBER-AUDIT.md ; instrument tools/audit_h_fiber.py ;
output out/p24_audit_h_fiber.txt ; repro py -3 -B -X utf8 tools/audit_h_fiber.py

STATUS OF THE AUDIT: all symbolic (sympy in r,b1,b2,A,H). The dps=50 block only
re-evaluates the same closed forms at fixed points (identity confirmation, NOT a
verdict source, NOT a search).

VERDICTS
 V1-V8  CONFIRMED exact (no correction needed):
   centre differences c1-c2 = 2r sin b1 (-cos b1,-sin b1), c3-c2 = 2r sin b2 (-cos b2,+sin b2);
   A+B = b1+b2 ; c9 = (s - H cos delta, -H sin delta) with delta = b1-A, s = sqrt(1-r^2);
   rho1^2 = (H^2+D1^2-2 H D1 cos A)/(4 sin^2 A), D1 = 2r sin b1;
   rho1 <= r  <=>  H in [2r sin(b1-A), 2r sin(b1+A)]   (roots = D1 cosA +/- sinA sqrt(4r^2-D1^2));
   root ordering automatic: 2r sin(b1+A) - 2r sin(b1-A) = 4 r cos b1 sin A > 0;
   combined lower H >= 2r |sin delta| ; upper H <= 2r min(sin(b1+A), sin(b2+B));
   |c9| <= 1-r  <=>  H^2 - 2 s cos(delta) H + 2 r (1-r) <= 0.
 V9  ADDITION: delta in (-b2, b1)  (equivalently A>0 and B>0). Not in the note.
 V10 ADDITION: cos delta > 0 is a SEPARATE necessary condition. The two hub-quadratic
   roots have product 2r(1-r) > 0 and sum 2 s cos delta, so both are positive iff
   cos delta > 0; if cos delta <= 0 the quadratic is >= 2r(1-r) > 0 for every H >= 0
   and the patch is EMPTY even when D = s^2 cos^2 delta - 2r(1-r) >= 0.
 V11 CONFIRMED exact: the pointwise closure makes three multiplier coefficients into
   constants -pi (site-2 angle slot), +pi (switch-angle slot 1), +pi (slot 2); hence
   the gain is booked only in coupled variables and the global constant is unchanged.
 V12 SCOPE: rho_j <= r is necessary because the face's Voronoi vertex lies in D and
   must be covered; the domain stays a NECESSARY patch domain (realization of the rest
   of the graph and the second hub are omitted).

EXPLICIT H-FIBER (r,b1,b2,A fixed; delta = b1-A; D = s^2 cos^2 delta - 2r(1-r)):
  H in [ max( 2r|sin delta| , s cos delta - sqrt(D) ) ,
         min( 2r sin(b1+A) , 2r sin(b2+B) , s cos delta + sqrt(D) ) ]
  preconditions: b1,b2 in (0,pi/2); delta in (-b2,b1); cos delta > 0; D >= 0;
                 sin(b1+A) > 0; sin(b2+B) > 0; nonempty <=> lower <= upper.
  When D >= 0 and cos delta > 0 the hub lower root s cos delta - sqrt(D) is > 0
  automatically (since D < s^2 cos^2 delta).

NOT DONE (explicitly open): the two tips' cross-conditions |T1-c3| >= rho1 and
|T2-c1| >= rho2 (tips must not be nearer the neighbouring patch ring) and the
second-hub conditions; both would only shrink the fiber, so the fiber above remains a
SAFE necessary description but not yet the maximal necessary one.

NO numeric maximisation was run (per instruction); nothing here is an upper bound,
a certificate, or a claim about the sharp value.

ROUND 11 — CORRECTIONS FROM LEAD REVIEW (append-only; supersedes the wording in the
ROUND 11 block above where it conflicts):

 X1 WITHDRAWN: my V10 ("cos delta > 0 is a separate necessary condition") is WRONG as a
    domain restriction and is withdrawn.  Since b1,b2 in (0,pi/2), the note's inline
    A,B>0 gives delta in (-b2,b1) SUBSET (-pi/2,pi/2), hence cos delta > 0 automatically.
    The root-positivity computation (product 2r(1-r) > 0, sum 2 s cos delta > 0) remains
    only as a consistency check; D >= 0 is the sole emptiness test from hub interiority.
 X2 REFRAMED: my V9 is a RESTATEMENT of the note's inline A,B>0, not an addition.
 X3 UNITS (new section 6 of H-FIBER-AUDIT.md): u2 = v2 = t = r/R0 in the dual/atom
    normalization (R0 = 19/50); u2 = v2 = 1 only in r-units.  w2 = 2 asin(R0 t) = 2 asin r.
    The H-fiber inequalities are geometric (r-units) and unaffected; only the atom
    arguments convert by the factor r/R0 when the seven atoms are summed.
 X4 No further jobs started; no numeric maximisation, no LP re-optimisation, no claim.

Net audit verdict: the lead's main proof is correct as written (V1-V8, V11 confirmed
exactly, symbolically).  Deliverables: H-FIBER-AUDIT.md; tools/audit_h_fiber.py;
out/p24_audit_h_fiber.txt.

================================================================================
ROUND 12 — H-DEPENDENCE OF THE PATCH FACE ATOMS (own files only; no claims)
================================================================================
Deliverable: H-FIBER-H-DEPENDENCE.md ; instruments tools/h_dependence.py,
tools/h_curvature_check.py, tools/h_endpoint_max.py, tools/telescoping_check.py,
tools/fullsum_h.py ; outputs out/p25..p29.

EXACT RESULT (verified: closed form = verbatim mirror of the lead's atom code to 1e-15
at five points; F' vs direct finite differences 6e-9; F'' vs dF'/dH 1e-10):
  F(H) = C0 + lam0 H + a1 phi1 + a2 phi2 + b1s L1^2 + g1 L1 + b2s L2^2 + g2 L2
  phi_j = atan2(D_j sin th_j, H - D_j cos th_j), L_j = sqrt(H^2+D_j^2-2 H D_j cos th_j)
  lam0 = R0(sin b1 sin A + sin b2 sin B) > 0  (the two face VALUES: v1+v2 = lam0 H)
  a1 = (z1+zang[e92])-(z9+zang[e12]), a2 = (z3+zang[e92])-(z9+zang[e23])
  b1s = sgn(f1,e91) z11[e91]/(4R0^2), g1 = sgn(f1,e91) z73[e91]/(2R0), similarly (3,9)
  F'' = 2(b1s+b2s) + sum_j [2a_j D_j sin th_j (H-D_j cos th_j)/L_j^4 + g_j D_j^2 sin^2 th_j/L_j^3]
      = 2(b1s+b2s) + sum_j sin^3(phi_j)/(D_j sin th_j) * [2a_j cos(phi_j)/(D_j sin th_j) + g_j]
Shared-edge (9,2) slots cancel IDENTICALLY (t_j sin psi_j = H/(2R0) in both faces, signs opposite).

FROZEN COEFFICIENTS (lead/joint_patch_frozen_v2.json): b1s=+0.703356672, b2s=+0.728753523,
g1=-1.151106437, g2=-1.188609458, a1=+0.011949606, a2=+0.012762705 (edge-angle slots are 0
on the five patch edges). Cross-check: the lead's quotes +.406258814, +.420928035,
-.874840892, -.903343188 are exactly sgn*z11, sgn*z73 = 4R0^2*b1s, 4R0^2*b2s, 2R0*g1, 2R0*g2.

NEGATIVE RESULT (this is the answer to "check endpoint max, do not assume"):
 - the sign-free convexity bound is VACUOUS here: M >= (|g1|+|g2|)/(2R0) = 3.078574 >
   2(b1s+b2s) = 2.864220 ALWAYS, so no uniform curvature bound can give endpoint-max;
 - H-endpoint-max is FALSE for the two-face object: with the frozen coefficients there are
   admissible (b1,b2,A) whose fiber has an INTERIOR argmax, with the gap over the best
   endpoint reaching +4.25e-02:
     (0.8,0.8,0.8) fiber [0.3050,0.7597] argmax H=0.49584 gap +4.25e-02
     (0.6,0.6,0.6) fiber [0.3050,0.7083] argmax H=0.37507 gap +1.65e-02
     (0.5,0.5,0.4) fiber [0.3073,0.5953] argmax H=0.32464 gap +1.63e-03
     (1.1,0.7,0.9) fiber [0.3144,0.6911] argmax H=0.61291 gap +3.27e-04
   (in each, F'(Hlo) > 0 > F'(Hhi): an interior critical point exists);
 - correct reduction for that object: endpoint evaluation PLUS the zeros of the displayed
   scalar F' (atan2 derivatives -D_j sin th_j/L_j^2). Endpoint-max only if F' has no sign
   change on the fiber.

NEW STRUCTURAL FACT (telescoping; independent of z and of the chart):
 - for EVERY internal edge, the z11 and z73 slots cancel identically over its two incident
   faces (both see the same edge length: t_f sin(theta_f^opp) = |e|/(2R0));
 - hence in the full 11-face sum those slots survive only on the 9 LEAF edges, which in the
   q0(6,7) graph are the ring-ring edges (0,1)...(8,0) — all H-INDEPENDENT;
 - verified: the full-sum z11/z73 contribution is -12.081921165806 at H=0.30,0.40,0.50,0.60
   with spread 3.6e-14.
 - CONSEQUENCE: the full sum has NO sqrt-of-quadratic and NO H^2 terms in H; its
   H-dependence is (piecewise affine face values) + (angle slots = atan2 terms) over the six
   hub-9 faces. If the lead's gauge accounting (mu2/cl113/cl114 -> 9pi) already uses this
   cancellation, the H-fibre is governed by that reduced form (F'' = sum of single-sign-change
   terms 2D sin th (H-D cos th)/L^4, so F''_full can change sign but only finitely often),
   and endpoint-max must still be TESTED.

NOT DONE: no certificate, no rigorous upper bound, no re-optimisation, no claim registered.

ROUND 12 — CORRECTIONS FROM LEAD DECISION (append-only; supersedes the Round-12 block above)

 C1 LAMBDA CAVEAT (lead correction, accepted): the face-value term carries the ACTUAL
    allowance r, NOT R0:
       v1 + v2 = r * ( sin b1 sin A + sin b2 sin B ) * H
    (each face value is its area (1/2) D_j H sin theta_j with D_j = 2r sin b_j).  My earlier
    "lam0 = R0(...)" is valid only on the maximal-allowance slice r = R0 and every number in
    the Round-12 block was evaluated at r = R0 = 0.38; they must be read as that slice.
    The chart, the H-FIBER-AUDIT inequalities and D_j = 2r sin b_j already use the actual r.
 C2 STATUS DOWNGRADE (lead instruction): the four interior-argmax rows are NUMERIC instances
    in double precision at r = R0, WITHOUT an interval witness.  They are evidence that
    "endpoint max" is not a theorem, NOT a proof that it fails, and they say nothing about the
    certificate's actual fiber position.  A rigorous version would need an interval-witnessed
    (b1,b2,A) with certified sign change of F' and a certified gap over both endpoints.
    What IS exact and retained: F, F', F'' and the trigonometric form of F''.
 C3 SCOPE (lead decision): the certificate patch keeps the TWO site faces only, so the
    external sqrt terms STAY and the two-face object is the relevant one.  The full-sum
    telescoping S2 is already known/matching to the lead and is IRRELEVANT to the patch
    certificate; recorded here only as a consistency check of the two-face bookkeeping.
 C4 Correct reduction for the patch certificate: 1-D maximisation of the explicit F over the
    fiber H in [Hlo,Hhi] — endpoint values PLUS the zeros of the displayed scalar F'
    (atan2 derivatives -D_j sin th_j/L_j^2); sqrt terms stay in F, F', F''.
 C5 No further jobs started; no claim registered; no mainTarget change.

================================================================================
ROUND 13 — (a) width-polynomial audit, (b) width-guard logic audit
================================================================================
(a) lead/WIDTH-STATIONARY-POLYNOMIAL.md (+ JOINT-PATCH-SEPARABLE-FIBERS.md inputs).
    Independent sympy audit, tools/audit_width_polynomial.py, out/p30_width_poly_audit.txt.
    VERIFIED EXACT (no discrepancy found):
      A1  clockwise parametrisation P(w)=R(-w)P1 with y=tan(w/2): p == Pnum/Q,
          x == Xnum/Q, D == Dnum/Q  (all True, exact identities);
      A2  A*Q^2 == Anum with A = D(1-p+2h)+2k(1-p)+4d D x/R0^2  (True);
          the identity 2D F' = A + 2 l x sqrt(D)/R0 also checks out term by term;
      A3  G == Q^4 (A^2 - 4 l^2 x^2 D/R0^2)  (True), degree of G in y = 8 exactly, and the
          y^8 coefficient is a nonzero polynomial in the parameters => "degree <= 8" and
          "at most 8 real stationary candidates" are correct as stated.
    PARTIAL: the A4 block (symbolic verification of the four unsquared derivative identities
      alpha'=(1-c.P)/d^2, (u^2)'=-2cross(c,P)/R0^2, (sector area)'=(1-c.P)/2,
      (L+w/2)'=1-alpha', and of F1' assembly) timed out in the runner (600 s) before printing
      its booleans; those identities were derived by hand in the same round and are consistent
      with the code's `grad`, but the symbolic run did NOT complete — status: hand-checked, not
      machine-verified. A3's degree/coefficient output is complete.
(b) read-only logic audit of lead/interval_joint_patch.py + interval_patch_fibers.py
    (focused question on the width mean-value guard). Deliverable WIDTH-GUARD-LOGIC-AUDIT.md.
    VERDICT: YES, the guard is exactly the domain-of-validity test: `sector` has exactly three
    value-changing operations (d2-clip to [(R*19/100)^2, r^2]; pos(orient) with None if
    orient.b<0; pos(lc) with None if lc.b<0), and widthbound recomputes the same three
    quantities with the same formulas on the same (r,b,w) box and compares against the OUTER
    endpoints of the constants (dd.a vs ((R*I(19)/100)^2).b; dd.b vs (r*r).a; orient.a>0;
    lc.a>0). Guard passing => clamps identity for all outer parameters and the whole segment,
    u >= 19/100 > 0, the analytic branch (alpha, L in (0,pi)) is fixed, so `center` encloses
    F(mid) and the mean-value step with the verified `grad` is valid; intersecting with raw is
    valid. Two refinements, no gap: the dd-upper test uses (r*r).a where the clamp uses
    (r*r).b (stricter than necessary, conservative), and mid is always inside [w.a,w.b].
    CONCRETE CAVEATS REPORTED: (G1) the fallback `return raw` on a guard-failing box is NOT
    covered by the guard; with the current frozen signs the dd-clamp and orient-clamp raise the
    value (valid upper bounds) but the lc-clamp LOWERS h(L+w/2) because h<0, so a lc-failing box
    can under-estimate and must be refined/rejected rather than treated as evaluable; (G2)
    interval_joint_patch.evaluate calls the same sector with no guard at all (its filters check
    b-range, X>0, w.a<=W.b, hub norm, face radii — not dd/orient/lc), so if that path feeds a
    certified number it needs the same guard.

ROUND 13 ADDENDUM — WITHDRAWAL + COMPLETED POLYNOMIAL AUDIT
 X1 G1/G2 WITHDRAWN as invalid (lead ruling, accepted; full text in WIDTH-GUARD-LOGIC-AUDIT.md
    section 3). Reasons recorded: (a) the sector interval encloses the function on the ACTUAL
    FEASIBLE patch subset of the box, where lc>=0, orient>=0 and the distance bounds hold BY
    GEOMETRY; intersecting with that necessary range is standard interval constraint
    contraction, no sign-monotonicity assumption is involved, and not enclosing unphysical
    points is intentional; (b) only the mean-value step must extend over all outer parameters
    of the segment, which is what the guard tests, so the `raw` fallback needs no guard;
    (c) my quoted multiplier signs came from the older joint_patch_frozen_v2.json, not from the
    current joint_nested_frozen.json.
    The guard proof (WIDTH-GUARD-LOGIC-AUDIT.md section 2) STANDS unchanged.
 X2 UNSQUARED DERIVATIVE IDENTITIES now MACHINE-VERIFIED EXACT (this completes the
    WIDTH-STATIONARY-POLYNOMIAL.md audit). Method: explicit differentiation of the atan2
    expressions (so no atan2 survives), then polynomial division of the difference by the two
    constraints P1x^2+P1y^2=1 and cos^2 w+sin^2 w=1; all remainders are 0:
      id0 dP/dw = -J P ;
      id1 alpha' = (1 - c.P)/d^2 ;
      id2 (orient/2)' = cos w - c.P  [equivalently (triangle area)' = (1-c.P)/2 - (1-cos w)/2] ;
      id3 (u^2)' = -2 cross(c,P)/R^2 ;
      id4 (L + w/2)' = 1 - alpha' ;
    hence by linearity the assembled derivative equals the code's `grad` expression exactly.
    Together with the earlier exact results — A1 (p=Pnum/Q, x=Xnum/Q, D=Dnum/Q),
    A2 (A Q^2 = Anum and 2D F' = A + 2 l x sqrt(D)/R), A3 (G = Q^4 (A^2 - 4 l^2 x^2 D/R^2),
    degree of G in y = 8 EXACTLY with nonzero y^8 coefficient) — the whole polynomial chain
    of lead/WIDTH-STATIONARY-POLYNOMIAL.md is verified with no discrepancy found.
    Harness note: an earlier run printed False for id1/id2/id4; that was my own harness defect
    (a "+1" typo in the id2 test string and an incomplete polynomial reduction), not a
    discrepancy in the lead's document. Fixed; an independent dps=30 numeric check at a generic
    point agrees to 1e-19.
 X3 No further jobs; no claim registered; no mainTarget change.

================================================================================
ROUND 14 — C849 neighbour-centre eta/alpha/L identities and uniform bounds
================================================================================
Deliverable C849-ETA-IDENTITIES.md; instrument tools/c849_identities.py;
output out/p32_c849_identities.txt. Own files only; no claim registered; no kernel re-audit.

EXACT RESULTS:
 T1 eta(w) = arg(P(w)-c) - arg P(w).  Proof: conj(c)P = (c.P) + i cross(c,P), so
    1 - conj(c)P = (1-c.P) - i cross(c,P) => eta = -arg(1 - conj(c)P); and
    (P-c)conj(P) = 1 - c conj(P) whose conjugate is 1 - conj(c)P, giving
    arg(1-conj(c)P) = arg P - arg(P-c).
 T2 alpha = w + eta1 - eta(w) (with eta1 := arg(P1-c) - theta1 = eta(0), theta1 = -asin r);
    L + w/2 = pi/2 + eta(w)  (chord direction = theta(w) + w/2 + pi/2, direction P->c =
    theta(w) + eta(w) + pi).
 T3 eta1 = 2b + asin r - pi/2 exactly: P1 - c = r(sin 2b, -cos 2b) (verified exactly) hence
    arg(P1-c) = 2b - pi/2, and P1 = (cos phi, -sin phi) so theta1 = -asin r.  On the domain
    eta1 in (0, pi/2 - asin r].
 T4 |c|^2 = 1 + r^2 - 2 r sin(2b + asin r) exactly (sympy difference identically 0); on
    b in (acos(r)/2, acos(r)] this gives (1-r)^2 < |c|^2 <= 1-r^2, i.e. 1 - r < |c| <= s < 1
    (equality |c| = s exactly at b = acos r).  Hence 1 - c.P >= 1 - |c| >= 1 - s, and since
    1 - s >= 1 - sqrt(55)/8 at r = 3/8, with the EXACT comparison 1 - sqrt(55)/8 > 1/14
    (<=> 2704 > 2695):  1 - c.P > 1/14 > 0 uniformly for r in [3/8, 19/50].
 CONSEQUENCES: (a) |eta| < pi/2 and eta smooth on all of R — no atan2 branch crossing, so
    alpha = w + eta1 - eta(w) is smooth for all w and is the UNWRAPPED alpha (the physical
    sector is its restriction alpha in [0,pi]; the formula extends past the flat endpoint
    alpha = pi at w = w_pi); (b) d^2 = |P-c|^2 <= (1+s)^2 <= (1+sqrt(55)/8)^2 = 3.713425 < 4;
    (c) alpha' = (1 - c.P)/d^2 > (1/14)/4 = 1/56 > 0 (consistent with the previously
    machine-verified alpha' identity), so alpha is strictly increasing in w and alpha = pi
    occurs at exactly one w.
 CALIBRATION: dps=40 identity agreement to the printed 10 digits at five (r,b,w) points;
    the (0.375,1.1,1.4) row differs by 2pi only because the harness extracted alpha through
    atan2 in (-pi,pi], and at w=0 the harness's raw L is 0 because the triangle is degenerate
    (the identity gives the correct tangent-chord limit L(0+) = 2b + asin r in (pi/2,pi)).

================================================================================
ROUND 15 — audit of lead/LOCAL-HUB-RIDGE-ELIMINATION.md + its three certificates
================================================================================
Deliverable HUB-RIDGE-AUDIT.md; instrument tools/ridge_independent_check.py;
output out/p33_ridge_independent.txt. Own files only; no lead edits; LOCAL scope only.

VERDICT: no concrete discrepancy.  The inference chain closes:
 FH'>0 on the projected fiber (certified >=.324122527) => for each delta with nonempty C848
 fiber the sup over H is at H_max(delta)=min(h1,h2); on Q both sine arguments lie in (pi/2,pi)
 => h1 increasing and h2 decreasing in delta => H_max=h1 for delta<=delta*=b1-b2 and h2 after;
 the two branch derivatives have strictly opposite signs => the first branch increases up to
 delta* and the second decreases after it; the ridge point is strictly feasible and the branches
 meet there => sup on Q0 is at (delta*,H*).  Widths are independent of delta and H; the box is
 asymmetric and the Q0 restriction b1 in [1.106,1.108] gives delta* in [0.035,0.040], so no WLOG.

INDEPENDENT CONFIRMATIONS (my own chart code, mpmath dps=40, current joint_nested_frozen.json):
 - ridge trig data: phi1-b1, phi2-b2, L1-2r sin b2, L2-2r sin b1 all = 0 to 1e-41; h1=h2=H*
   = 2r sin(b1+b2) exactly (both face uppers saturated exactly);
 - radical-free form: direct two-face FH at the ridge minus the radical-free expression = 0 to
   1e-41, factor 4 confirmed (each face contributes H r sin b1 sin b2 = 2r^2 sin(b1+b2) sin b1 sin b2);
 - branch orientation: 2b1-delta in [2.170,2.181], 2b2+delta in [2.171,2.182] both inside
   (pi/2,pi); dh1/ddelta in [.4286,.4344]>0, dh2/ddelta in [-.4350,-.4293]<0;
 - chain rule / 2R normalization: my own central finite differences of (z3-z1)+d/ddelta FH
   along both branches agree with the coded analytic expression to 1e-22 at four tuples; the
   factors (Hd y+H yd)/2, az(x yd-y xd)/Q, bz Qd/(4R^2), gz Qd/(4R sqrt(Q)) with ee=sqrt(Q)/(2R)
   are all correct, as are td=-/+1 and Hd=-/+2r cos(arg);
 - feasibility: sep=H*-2r|sin delta*| in [.5940,.5970]>0 and norm=H*^2-2s cos(delta*)H*+2r(1-r)
   in [-.2941,-.2929]<0 at five tuples; norm<0 is the C848 hub condition and supplies the second
   lower bound via its roots, sep supplies the first;
 - coverage: FH' at the branch endpoints = +0.3722 (my own derivative), consistent with the
   certified lower bound; the H-projection hl/hh from interval_patch_delta.setup line 20 uses the
   outward endpoints of the C848 bounds, so it contains the actual fiber at every box point, and
   the active H (=h1 or h2) lies in the actual fiber, hence in the projected interval.
NOTES (documentation only, no inference gap): (N1) the script does not explicitly assert the
 remaining C848 upper H<=2r though it is immediate from its own recorded numbers (2r>=.758 >
 faceupper_upper=.6275965948); (N2) the "min switches branch at delta*" fact lives in
 certify_delta_ridge.py plus the (pi/2,pi) observation rather than in the h-monotone certificate;
 (N3) scope stays local/conditional as the .md states (box Q/Q0, frozen coefficients with
 z50..72=0, C849 relaxation, no global-cover or exterior claim).

================================================================================
ROUND 16 — C853 ridge feasibility domain (exact, global on the legal chart domain)
================================================================================
Deliverable C853-RIDGE-DOMAIN.md; instrument tools/ridge_domain_analysis.py;
output out/p34_ridge_domain.txt. Own files only; no kernel write; no objective-monotonicity
assumption used (feasibility only).

THE ONE NECESSARY-AND-SUFFICIENT INEQUALITY (ridge delta*=b1-b2, H*=2r sin(b1+b2), A=b2, B=b1):
 the C848 hub-norm condition is |c9| <= 1-r with residual
   R = H*^2 - 2s cos(delta*) H* + 2r(1-r) = |c9|^2 - (1-r)^2 = -2r*Phi,
 and Phi has the three verified-equal forms
   Phi = 2 s sin(b1+b2)cos(b1-b2) - 2r sin^2(b1+b2) - (1-r)
       = s(sin2b1+sin2b2) - 2r sin^2(b1+b2) - (1-r)
       = r cos(2b1+2b2) + s(sin2b1+sin2b2) - 1
 => RIDGE FEASIBLE <=> Phi >= 0 <=> r cos(2b1+2b2) + sqrt(1-r^2)(sin2b1+sin2b2) >= 1.
 Sufficiency: all other C848 constraints are automatic — both face upper bounds are SATURATED
 exactly (2b1-delta* = 2b2+delta* = b1+b2); the separation lower bound has the exact identity
 H* - 2r|sin delta*| = 4r cos(max b) sin(min b) > 0; H* <= 2r; and Phi >= 0 already forces
 disc >= 0 because otherwise the quadratic in H would be positive everywhere.
GLOBAL FEASIBILITY: bj in (acos(r)/2, acos(r)] forces w=sin(b1+b2) in (2rs,1] and
 cos(b1-b2) >= sqrt((1+r)/2); Phi is concave in w and increasing in cos(b1-b2), so
 Phi >= min(A,B) with A = (1+r)(sqrt(2(1-r))-1) and B = (1-r^2)(4r sqrt((1+r)/2) - 8r^3) - (1-r).
 Crude rigorous constants on r in [3/8,19/50]: A >= 0.1561, B >= 0.0635 > 0 => Phi > 0 on the
 WHOLE legal domain, hence a fortiori on every tuple with nonempty legal width fiber (bj >= bmin).
 Numeric scan (161x161 per r): min Phi = 0.16113/0.15811/0.15606 at r = 0.375/0.378/0.38,
 attained at the corner (acos(r)/2, acos(r)).  So the feasible (b1,b2) set is the entire legal
 domain — no exclusion region, no feasibility hole.
OBTUSE ARGUMENTS ARE INDEPENDENT: at the ridge both sine arguments equal b1+b2, so "obtuse"
 means b1+b2 > pi/2, which is NOT automatic (b1+b2 in (acos r, 2acos r] = (pi/2-phi, pi-2phi]);
 e.g. r=0.375, b1=b2=0.59379 legal gives b1+b2=1.18759 < pi/2 while Phi=+0.44943 — ridge
 feasible exactly where the arguments are ACUTE.  Ridge feasibility therefore does not need
 obtuseness, while the delta-elimination does (the branch-orientation hypothesis fails on a
 nonempty part of the global domain, e.g. near the lower corner bj ~ acos(r)/2; the lead's Q0
 box meets it, but that is box-specific).
DEGENERACIES: D1 sep=0 only at min b=0 or max b=pi/2 (both off-domain, so sep>0 strictly);
 D2 Phi=0 (|c9|=1-r) never attained (min ~0.156, rigorous >= 0.0635); D3 both face bounds
 saturated with equality, so the ridge is a boundary point of the H-fiber with zero slack;
 D4 the bound A vanishes only at r=1/2, outside r<=19/50; D5 b1=b2 (delta*=0) is a legal slice
 with Phi>0; D6 |b1-b2| -> acos(r)/2 is excluded strictly by the chart domain.

================================================================================
ROUND 17 — independent check of the (T,D,eps) cap identity and the (u,eps) chart
================================================================================
Deliverables C853-RIDGE-UNIFORM.md (uniform ridge feasibility) and C853-CONE-IDENTITY.md;
instruments tools/ridge_uniform_proof.py, tools/cone_identity_check.py; outputs out/p35, out/p36.

A. UNIFORM RIDGE FEASIBILITY (lead's threshold route) — PROVED, condition removed.
 norm/(2r) = 1 - r cos2T - 2s sinT cosD = (1-r) + 2r sin^2T - 2s sinT cosD = -Phi (exact).
 Condition <=> cosD >= f(v) = (1-r+2rv^2)/(2sv), v = sinT; f'' = (1-r)/(sv^3) > 0 so f is
 convex and sup over v in (2rs,1] is at an endpoint.  Endpoint v=1: f(1) <= c0 = sqrt((1+r)/2)
 <=> r <= 1/2 (exact, and r <= 19/50 < 1/2).  Endpoint v=2rs: f(2rs) <= c0 reduces to
 1 - r + 8r^3(1-r^2) <= 4r(1-r^2) sqrt((1+r)/2); LHS is increasing on r in [3/8,19/50]
 (L' = -1+24r^2-40r^4 >= 2.5409 > 1) so LHS <= 38890151/39062500 = 0.99558787 < 6417 sqrt(11)/20000
 = 1.06413906 <= RHS, with the exact integer comparison 777803020000^2 < 6417^2*11*39062500^2 TRUE.
 => hub-norm holds STRICTLY on the whole legal domain (true slack ~7.6%, worst endpoint v=2rs);
 ridge geometry feasibility is automatic, no (b1,b2) exclusion, condition removable.
 Still box-specific (objective-side): the obtuse-argument condition and the branch sign certificates.

B. CONE IDENTITY — CONFIRMED, with one refinement and one precision.
 * identity CORRECT: min sin(T+-eps) = sinT cos eps - |cos T sin eps| = sin(beta-|eps|),
   beta = min(T,pi-T); reparametrisation A=b2-eps, B=b1+eps, args T-+eps exact;
   verified numerically at nine (T,eps) pairs (T acute and obtuse, eps both signs, T near pi).
 * REFINEMENT: the identity needs only |eps| <= pi, not |eps| < pi/2; the latter is automatic
   here since A,B>0 give |eps| < max(b1,b2) < pi/2.  The binding condition is |eps| < beta
   (cap positivity), which is what yields the cone.
 * cap = 2r sin(beta-|eps|) is even, strictly decreasing in |eps|, maximised at the RIDGE
   (eps=0) in BOTH regimes, cap(0) = 2r sin beta = min(h1,h2): the ridge maximises the face
   H-cap globally, no obtuse hypothesis.
 * cone EXACT: H <= 2r sin(beta-|eps|) <=> |eps| + u <= beta with u = asin(H/2r) (beta <= pi/2
   and asin monotone on [0,pi/2]).  Linear triangle with vertices (0,0), (+-beta,0), (0,beta).
 * active-face flip: sin(T-eps) < sin(T+eps) <=> cosT sin eps > 0, i.e. the b1+A face is active
   iff eps cosT > 0 — flips at T = pi/2, both branches giving the same cap.
 * no missing arguments: A,B in (0,pi) with A+B = T => T-+eps in (0,2pi); nonempty fiber needs
   both face uppers > 0 => sin(T-+eps) > 0 => both arguments lie in (0,pi).  Confirmed.
 * PRECISION on "linear triangle fiber": the FACE CAP is exactly that triangle; the separation
   constraint sin u >= |sin(D+eps)| is piecewise linear in (u,eps) once the branch of delta=D+eps
   is fixed (u >= delta or u >= pi-delta), but the hub-norm constraint stays quadratic in sin u
   and is only automatic at eps = 0; for eps != 0 it is generally active and must be carried.

================================================================================
ROUND 18 — review of HUB-CONVEX-LENS-REDUCTION.md + CARTESIAN-HUB-DISK-INTERSECTION.md
================================================================================
Deliverable HUB-DISK-AUDIT.md; instrument tools/hub_disk_audit.py; out/p37_hub_disk_audit.txt.
Own files only; no kernel write; domain/equivalence review only (not objective convexity).

VERDICT: every structural claim in the two notes is CORRECT; two clarifications recorded.
 DISK FORMS exact (residuals 0 on a clean symbolic check; an earlier messy print was my own
 double-substitution artifact, redone correctly):
   hub-norm |c9|<=1-r <=> (v-s)^2+t^2 <= (1-r)^2 <=> H^2-2sHcos d+2r(1-r) <= 0;
   H <= 2r sin(2b1-d) <=> (v-r sin2b1)^2+(t+r cos2b1)^2 <= r^2;
   H <= 2r sin(2b2+d) <=> (v-r sin2b2)^2+(t-r cos2b2)^2 <= r^2 (centres have norm r, so
   H <= |c9-C|+|C| <= 2r is automatic);
   separation H^2 >= 2r|t| <=> v^2+(|t|-r)^2 >= r^2 <=> both disk exteriors v^2+(t-+r)^2 >= r^2;
   wedge -b2 < delta < b1 <=> v>0 and -v tanb2 < t < v tanb1.
 REDUNDANCY correct, proved two independent ways (external tangency 1 = (1-r)+r + reverse
 triangle inequality |X-(0,+-r)| >= 1-(1-r) = r; and the analytic |P+- - c9| >= 1-|c9| >= r with
 unit points P+- = (s,+-r)); valid for ALL r in (0,1); tangency at (v,t) = (rs, +-r(1-r)) where
 the exteriors hold with equality.
 CONVEXITY correct with one recorded dependency: the set is 3 closed convex disks intersected
 with an open convex wedge (angle b1+b2 < pi), hence convex; the second note's description
 ("three disks, outside two other disks, within the wedge") is NOT convex read literally —
 convexity holds precisely BECAUSE the exteriors are redundant, so it is a corollary of the
 redundancy theorem and deserves a cross-reference.
 FACE CIRCLES: |C1-C2|^2 = 4r^2cos^2T exactly (T=b1+b2); |M|^2 = r^2 sin^2T; the radical axis
 passes through the origin (|C1|=|C2|=r), so the intersections are 0 (H=0, illegal) and
 2M = (2r sinT cosD, 2r sinT sinD) = the ridge point on the ray delta=D with H = 2r sinT; its
 strict containment in the hub disk is C853-RIDGE-UNIFORM.md, outside-forbidden is automatic.
 At T=pi/2 the centres coincide (sin2b1=sin2b2, cos2b1=-cos2b2 exactly) so the two face disks
 are identical and impose no independent constraint; ridge still feasible; convexity unaffected.
 CLARIFICATIONS (needed for the word "EXACTLY", no error):
  (a) the disk form keeps only the UPPER root H <= 2r sin(b1+A); the coded C848 face condition
      is the full quadratic, i.e. H in [2r sin delta, 2r sin(b1+A)].  Dropping the lower root is
      legitimate exactly because hub-norm => separation => H >= 2r|sin d| >= 2r sin d; so the
      chain three disks + wedge => hub-norm => separation => lower roots => full C848 closes.
  (b) "at most three intervals" is safe but not sharp: the exterior removals are empty on the
      hub disk, so fixed v really gives ONE closed interval (as the first note says).
  (c) v >= s-(1-r) > 4r/5 confirmed on [3/8,19/50]: f(r)=sqrt(1-r^2)-1+r/5 decreasing,
      f(19/50) = sqrt(2139)/50 - 81/100 = 0.0009865 > 0 <=> 2 sqrt(2139) > 81 <=> 8556 > 6561.
 SCOPE: the notes' caveats are correct — removes a nonconvex constraint class and gives an exact
 Euclidean chart, but asserts nothing about objective convexity or about the maximum sitting at
 the ridge/intersection; consistent with the earlier rounds (F_H neither concave nor convex, and
 the unconstrained H-argmax can be interior).

================================================================================
ROUND 19 — C858 hub objective: witness + envelope assessment; two audit fixes
================================================================================
Deliverables C858-HUB-SCOPE.md, C858-ENVELOPE-ASSESS.md; instruments tools/cartesian_scope.py,
tools/witness_check.py; outputs out/p38, out/p39. Own files only; no kernel write.

WITNESS INDEPENDENTLY CONFIRMED (my own code, joint_nested_frozen.json):
 the point is strictly feasible (delta=-0.549024 lies in (-b2,b1), v>0, disk residuals
 -0.001387769 / -0.114776538 / -0.059581098, separation margin +0.087959); hub factor witness
 -0.45134479461042063891 minus ridge -0.4975006139586483194 = +0.04615581934822768048916,
 identical to the lead's certified interval.  So global ridge max is FALSE; the witness lies
 outside the C853 box (b1=0.9471,b2=0.9149), so C855 feasibility and the C853 local result stand.

CURVATURE ANATOMY (explains the failed cap): for L_j = |(v,t)-Q_j|,
 Hess(beta_j L_j^2 + gamma_j L_j) = 2 beta_j u u^T + (gamma_j/L_j)(I - u u^T): radial eigenvalue
 +2 beta_j > 0 (this is the whole 2.808 failure), tangential 2 beta_j + gamma_j/L_j <= -0.102866
 (j=1) / -0.110114 (j=2) since L_j <= 0.76.  The angle terms have eigenvalues +- a_j/L_j^2 with the
 positive eigendirection w_j = (X_j+Y_j, Y_j-X_j)/|.| = u rotated by -pi/4; so a valid concavity
 test is sum a_j (w.w_j)^2/L_j^2 <= sum |m_j| (1-(w.u_j)^2)/L_j, which passes with a factor ~32
 at L ~ 0.67.  Normal-cone alone is indeed insufficient.

ENVELOPE — PROMISING, with quantified losses (C858-ENVELOPE-ASSESS.md):
 (A) secant: beta_j L^2+gamma_j L <= m_j L with m1=-0.611640150, m2=-0.611090614 < 0; the envelope
     U_A = affine + a1 theta1 + a2 theta2 - |m1|L1 - |m2|L2 is concave whenever L_j >= a_j/|m_j|
     = 0.020995 / 0.021775; loss <= beta_j (0.38)^2 = 0.1014 per face (<= 0.203 total).
 (B) radial monotonicity: phi_j' <= -0.0782 < 0, so phi_j(L_j) <= phi_j(lambda_j) with the
     STRUCTURAL lambda_j = 2 r sin b_j sin theta_j (law of sines + circumradius constraint
     sin phi_j >= sin b_j); at the C853 box (lambda_j ~ 0.58) this beats the secant by ~0.07 per
     face and has no convexity defect.
 Exact envelope maximisation is the two-vector balance alpha = c1 u1 + c2 u2 - a1 grad theta1
 - a2 grad theta2 with alpha = (r(1-cost cos D), -r cos T sin D), c_j = the effective radial slope,
 grad theta_j of length 1/L_j; angle contributions a_j/L_j = 0.017 / 0.059 at the witness are small
 against c_j ~ 0.61, so the balance is norm-dominated and interval-tractable, and concavity makes
 KKT sufficient.  Limits: hub factor only (width-side slack untouched); envelope A's <=0.203
 overhead is comparable to the 0.046 ridge gap, so for tightness use B on boxes with certified
 lambda_j plus the angle cap sum a_j theta_j <= a1(pi-b1)+a2(pi-b2) <= 0.053745 (or the exact
 extremal-ray value of theta_j).
AUDIT FIXES applied to HUB-DISK-AUDIT.md per lead: H = |(v,t)| = |c9-c2|, NOT |c9| (conclusion
 H <= 2r unchanged since |C-c2| = r as well); and the exact floor form
 sqrt(2139)/50 - 231/250 > 0 via the single integer comparison 25*2139 = 53475 > 53361 = 231^2.

================================================================================
ROUND 20 — CORRECTIONS to the C858 envelope notes (lead's objections ACCEPTED)
================================================================================
Deliverable C858-CORRECTIONS.md; both C858 notes patched in place; no follow-up chain started.

WITHDRAWN (my errors, accepted in full):
 W1 tensor form: I wrote Hess(beta L^2+gamma L) = 2 beta u u^T + (gamma/L)(I - u u^T), dropping
    2 beta (I - u u^T).  Correct: 2 beta I + (gamma/L)(I - u u^T), i.e. eigenvalues 2 beta (radial)
    and 2 beta + gamma/L (tangential) — the eigenvalues I quoted were right, the tensor was not.
 W2 per-term concavity: in the orthonormal (radial,tangential) basis
      Hess(a theta - c L) = [[0, -a/L^2], [-a/L^2, -c/L]],  det = -a^2/L^4 < 0 for EVERY L,
    so the term is INDEFINITE at every radius and no threshold L >= a/c repairs the mixed
    directions.  Confirmed numerically (eigenvalues -0.874 and +0.000785 at L=0.7, a=.01284,
    c=.6116; the tiny positive one is ~a^2/(cL^3), which is the lead's cap term).
    My "U_A is concave wherever L_j >= a_j/|m_j|" and the "factor ~32" sentence were both wrong
    (the latter also used a malformed quadratic form: it dropped the negative part of the angle
    Hessian).  WITHDRAWN, as are the KKT-sufficiency and global-optimality claims built on it.
 W3 reduction B notation: the structural bound was written with theta_j, colliding with the
    Cartesian theta_j = atan2(Y_j,X_j) = phi_j -+ delta.  Restated with thC_j = the face angle at
    c2 (A for j=1, B for j=2): L_j >= 2r sin b_j sin(thC_j), L_j <= 2r sin(thC_j), from the law of
    sines plus sin phi_j >= sin b_j.  Derivation now written out; not to be propagated without it.
STILL VALID: the secant inequality beta_jL^2+gamma_jL <= m_jL (m_j = 0.76 beta_j + gamma_j < 0);
Y_j > 0 and the angle cancellation; the area identity; the disk/wedge geometry and convexity; the
witness verification; the "normal-cone alone is insufficient" observation.

CORRECT WHOLE-2x2 CRITERION supplied (the proof the lead asks for): with
 Hess U = sum_j [ -(c_j/L_j)(I - u_j u_j^T) + (a_j/L_j^2) M_j ], M_j = 2 w_j w_j^T - I trace-free,
 tr(Hess U) = -(c_1/L_1 + c_2/L_2) < 0 AUTOMATICALLY, and in 2D NSD <=> tr <= 0 AND det >= 0, so
 concavity is the single scalar inequality
   det(Hess U) = -(a_1^2/L_1^4 + a_2^2/L_2^4) + c_1c_2/(L_1L_2) - tr(H_1H_2) >= 0,
 the only orientation-dependent term being tr(H_1H_2) (equivalently the angle between u_1,u_2).
DERIVED SUFFICIENT CONDITION (partial): using w^T M_j w <= 1 and
max_alpha[cos^2 alpha + cos^2(alpha-phi)] = 1 + |cos phi|,
 sum_j a_j/L_j^2 <= (1 - |cos phi|) min_j(c_j/L_j)  ==>  U concave.
 Numbers: at L = (0.6654,0.6785) this needs phi >= 20.66 deg; at the witness (L=0.7464,0.2257) it
 needs phi >= 49.21 deg.  So concavity holds when the radial directions are separated and becomes
 vacuous as they align — a real but PARTIAL sufficient condition, not a global claim.

================================================================================
ROUND 21 — audit of HIGH-BEARING-BOUNDARY-THEOREM.md / certify_hub_laplacian.py (C861)
================================================================================
Deliverable C861-AUDIT.md; own files only; no kernel write; no grids rerun.
VERDICT: the reduction is CORRECT on r in [3/8,19/50], bj in [1,acos r].

1 LAPLACIAN EXACT: Delta F = 4(beta1+beta2) - c1/L1 - c2/L2 with c_j = |gamma_j| =
  1.145102454 / 1.138494697.  The angle terms are HARMONIC (each theta_j is the polar angle of an
  affine map whose linear part is orthogonal), Delta(beta L^2) = 4beta, Delta(gamma L) = gamma/L.
  Numeric second-difference check at h=1e-6, dps=30: 1.26444131789 vs 1.26444131788 and
  1.66816187114 vs 1.66816187114 (11 digits).
2 RECIPROCAL CAP CORRECT, vertex argument made explicit: L_j <= 2r and L1+L2 >= d with
  d^2 = (D1-D2)^2 + 2D1D2(1-cos(b1+b2)) >= 16 r^2 sin^4(1) (b_j >= 1, b1+b2 >= 2) gives
  d >= 4r sin^2 1 = 2r(1-cos2); (L1,L2) -> c1/L1+c2/L2 is convex, so its max over the polygon is at
  a vertex: max(c1/a+c2, c1+c2/a)/(2r), a = -cos2 = 0.416146836547.  Values 5.186898 (larger),
  5.174537, 3.0047.  Cap ~ 1/r while 4 sum beta = 5.583507299 is r-free => worst at r = 3/8:
  Delta F >= 0.396609219 > 0.3966 => F strictly SUBHARMONIC => no interior maximum.
3 WEDGE BRANCH AUDITED AND HOLDS: the face constraint is exactly L_j <= 2 r sin(thC_j)
  (thC_1 = A, thC_2 = B), since the C848 face quadratic IS L_j^2 - 4r^2 sin^2(thC_j).  On A = 0
  this forces L1 = 0 (hub at c1), and the hub-norm disk excludes c_j: with c1 = (D1cos b1, D1 sin b1)
  in the (v,t) chart, |c1-(s,0)|^2 - (1-r)^2 = 2r[(1-r) + 2r sin^2 b1 - 2 s sin b1 cos b1], whose
  bracket is >= 1.151 - 0.843 > 0 on the domain (comfortable margin).  Hence the wedge edges meet
  Omega in the empty set, Omega is compact, its boundary lies in the union of the three circles, and
  the maximum of F is on those arcs.  Omega also keeps distance > 0 from every Q_j, so F is C^2 —
  the maximum-principle step needs no singular handling.
4 PRESENTATION POINTS: (P1) L_j <= 2r powers the cap; L_j <= 2r sin(thC_j) kills the wedge edges —
  keep them apart, the wedge step does not follow from L_j <= 2r alone; (P2) a = -cos2 needs
  b1+b2 >= 2, so b_j >= 1 is essential (high bearings only); (P3) b_j <= acos r is legality only,
  r enters via the 1/r cap scaling and D_j >= 2r sin 1; (P4) no ridge assumption and no objective
  concavity is used — the content is "interior eliminated, maximum on three arcs" (2D -> 1D).

================================================================================
ROUND 22 — C862: extension checks + bounded search over the complement d/(2r) < 1.38
================================================================================
Deliverable C862-LOW-DISTANCE-PROBE.md; fresh driver tools/probe_low_distance.py;
out/p40_low_distance.log, out/p40_low_distance_probe.json. Own files only; exploratory.

LOADER FINDING: probe_nested_patch.py -> check_arc_chart.py -> check_joint_reduced.py, and the
latter loads the OLD joint_patch_frozen_v2.json.  My driver runs the same chain but overrides the
exec'd namespace z with the CURRENT joint_nested_frozen.json; override verified effective
(exec-chain reduced() at a fixed chart point: 27.706996098 with current z vs 27.761340538 with v2),
and the detail path agrees with the summed objective to <1e-8.
RESULT (2 seeds, popsize 12, maxiter 80, polish, ~5400 evals each):
 seed 8620: 28.104237696621  r=.37999925 b1=.847522 b2=.838669 A=1.538698 delta=-.691176
            H=.521025 w1=.544618 w3=.530720 d/(2r)=1.115135
 seed 8621: 28.104240583963  r=.37999981 b1=.836817 b2=.847269 A=.145509 delta=+.691307
            H=.521232 w1=.527760 w3=.544230 d/(2r)=1.113042
 BEST in complement = 28.104240583963 ; gap to the 28.107045 threshold = 0.002804416.
 => the low-distance branch is NOT far below: it is within 0.0028 of the threshold, so it cannot
    be discarded by a crude bound and needs the general hub optimizer / strong coupling.
 Structure: r pinned at .380; b1,b2 ~ .837-.847 (LOW bearings, outside the C861/C862
 high-distance region); delta ~ +-0.691 with A,B strongly asymmetric (.145 / 1.539); H at the top
 of a nearly degenerate fiber; binding constraints are the corresponding face disk (0 / 2.8e-17)
 and the hub-norm disk (-1.9e-6 / -3.9e-9); wedge margins strictly positive (.1455); width
 margins ~.48.  The two seeds are mirror images (delta -> -delta, b1 <-> b2) - a consistency check.
EXTENSION CHECKS (HUB-BOUNDARY-ASYMMETRIC-EXTENSION.md): d >= 2r(sin^2b1+sin^2b2) holds with
equality at b1=b2 (numerically: b1=b2=1.1 gives d/(2r)=1.5884 vs S+S'=1.5885); the clean form
d/(2r) = sqrt(1+cos^2T-2cosT cosD) reproduces it; the wedge identity |c_j|^2-(1-r)^2 =
2r[1-cos(2b_j-acos r)] is EXACT (cos x0 = sin(2b_j+asin r) = 2s sinb_j cosb_j + r(cos^2b_j -
sin^2b_j)), so the wedge-edge exclusion extends past b_j>=1 as claimed; and the uniform bound
4(beta1+beta2) - (4/3)max((50/19)c1+c2, c1+(50/19)c2) = 5.583507299 - 5.5358956 = 0.047611
matches the note.  LIMITS: exploratory only (no sampling -> certificate); a larger budget could
only raise the complement value, so "not far below" is one-sided safe; the optima are
multi-binding with a collapsing H-fiber, so a follow-up bound for this branch must handle the
degenerate-fiber interface.

================================================================================
ROUND 23 — C862b: interior critical points / ND points of the hub objective
================================================================================
Deliverable C862b-INTERIOR-CRITICAL.md; drivers tools/interior_critical_probe.py,
tools/widthlegal_nd_probe.py, tools/check_p41_points.py; out/p41*, out/p42*.
Exploratory diagnostic only (400 samples + 4 x (2 seeds x 80 DE)); NOT a certificate.

HESSIAN VALIDATED: Hess F = 2(beta1+beta2)I - sum (c_j/L_j)(I - n_j n_j^T) + sum (a_j/L_j^2)M_j.
Calibration over 40 random legal points: worst |analytic - numeric| = 3.85e-4 with the (n,n^perp)
form [[0,-1/L],[-1/L,0]] (w_j = n_j rotated by -pi/4), versus 7.7e1 with the opposite convention.
STRUCTURAL PINCH (necessary for ND): testing w = n_1, n_2 gives
 c2/L2 + a2/L2^2 >= 2 sum beta = 2.791753650 => L2 <= 0.419177 and L1 <= 0.421097, and
 tr <= 0 gives sum c_j/L_j >= 5.5835.  So ND only lives in a small pinched region.
RESULTS:
 (a) 400 random legal samples: 0 ND; min lambda_max = 0.2957; lambda_max in [0.296, 585.4];
     min |grad| = 0.0623.  Random inspection is indeed not enough.
 (b) DE min lambda_max: ND points EXIST.  Chart-legal corner lambda_max = -0.6555
     (r=.375, b1=b2=.5932, delta=-.0023, H=.5816, sum c/L=6.90); and in the WIDTH-LEGAL domain
     lambda_max = -0.466954 at r=.37500, b1=.61258, b2=.61257 ( = bmin(0.375) ), delta=-.00230,
     H=.60039 strictly interior to [0.30203, 0.70505].  => the global positive-eigenvalue
     hypothesis is FALSE; the witness is nearly explicit (symmetric b1=b2=bmin, delta~0, r=3/8,
     H~0.6004) and is a realistic interval-certificate target.
 (c) DE min |grad|: interior STATIONARY points exist and are width-legal (b >= 0.66 > bmin):
     seed 86240: |grad|=4.1e-9, r=.37958 b1=.90923 b2=.83226, eigen=(+0.0565,+1.3560) => local MIN;
     seed 86241: |grad|=7.9e-11, r=.37615 b1=.91646 b2=.66756, eigen=(-2.2704,+2.1860) => SADDLE.
     Both verified INTERIOR to the lens (H strictly inside the fiber, wedge interior).
 (d) NO point was found that is BOTH stationary AND ND (ND points have |grad| ~ 0.73; stationary
     points have lambda_max > 0).  Since an interior local max needs exactly grad = 0 AND Hess <= 0,
     this diagnostic finds no interior local maximum.
CONSEQUENCE: concavity cannot be the explanation for boundary-only maximisation (ND points exist);
the viable route is to minimise |grad F| OVER the ND region (or lambda_max + mu|grad|) — a small
pinched 5-parameter obligation, not a global one.  Limits: "not found" is not "does not exist"; the
one-sided information is the ND existence, whose certification is the natural next step.

================================================================================
ROUND 24 — C862c: sign audit, exact reduction, corrected diagnostics
================================================================================
Deliverable C862c-PINCHED-STATIONARITY.md; drivers tools/sign_audit.py,
tools/corrected_diagnostics.py; outputs out/p43_sign_audit.txt, out/p43.log, out/p43_corrected.log.

1 SIGN AUDIT (the critical item): in the lead's coordinates the two angle terms have OPPOSITE
  chirality — symbolically grad theta1 = (-Y1,-X1)/L1^2, grad theta2 = (-Y2,+X2)/L2^2, n1 =
  (X1,-Y1)/L1, n2 = (X2,Y2)/L2, and <n1,Hess(theta1)n1^perp>L1 = +1 while
  <n2,Hess(theta2)n2^perp>L2 = -1.  Hence M1 = -(2w1w1^T-I), M2 = +(2w2w2^T-I) and
  Hess F = 2(beta1+beta2)I - sum (c_j/L_j)(I-n_jn_j^T) + (a1/L1^2)M1 + (a2/L2^2)M2.
  Radial entries n_j^T M_j n_j = 0 are sign-independent (so the pinch is safe); every MIXED
  statement flips with the chirality, and Round 23 used the same chirality for both terms, i.e. a
  neighbouring function.  Corrected formula re-calibrated against finite differences: worst
  |analytic-numeric| = 5.47e-4 over 30 legal points.
2 EXACT REDUCTION — interior local max => (R1) c_j/L_j + a_j/L_j^2 >= 2 sum beta (=> L1<=0.421097,
  L2<=0.419177); (R2) tr Hess = 4 sum beta - sum c_j/L_j <= 0; (R3) det >= 0 i.e.
  (tr/2)^2 >= ((H11-H22)/2)^2 + H12^2 (the only chirality-sensitive condition); (R4) stationarity
  alpha = sum c_j n_j - sum a_j grad theta_j with alpha = (r(1-cosTcosD), -r cosT sinD).
  (R1)+(R2) alone are satisfiable (the ND witness has L~0.35, sum c/L~6.7), so excluding interior
  maxima needs (R4) (and (R3) for the semidefinite case) — i.e. a linear combination of grad F
  that never vanishes on the pinched region, or the 4-parameter system (L1,L2,phi,angle(alpha)).
3 CORRECTED DIAGNOSTICS (2 seeds x 80 each): ND points still exist and stay width-legal —
  min lambda_max = -0.572099 (lam_min -0.572381) at r=0.375, b1=b2=0.61254~bmin, delta=-0.0022,
  H=0.58464 interior, sum c/L=6.728, trace=-1.145.  Interior STATIONARY points exist (|grad|~1e-9,
  width-legal, H interior) and are SADDLES: eigen (-0.7416,+1.7718) and (-0.0022,+1.4276).  The
  second has lambda_min within noise of ZERO, i.e. stationary configurations approach SEMIDEFINITE
  Hessians — exactly the case the lead flagged, so the exclusion must be stated with <= 0 / >= 0
  and cannot rest on strict negative definiteness.
4 LIMITS: numeric parts are exploratory; formula parts (1) and (2) are exact.  Round 23's direction
  survives but its eigenvalues were those of a slightly different function; the re-run supersedes.

================================================================================
ROUND 25 — C862d: interface fixed; three errors corrected; numerics stopped
================================================================================
Deliverables: corrected C862b/C862c notes; new tools/interface_check.py; out/p44_interface.log.
Own scope.  Numeric work stopped as instructed until the interface was fixed (it now is).

1 INTERFACE CHECK (the lead's demand: audit the CODE objective, not my own construction).
  tools/interface_check.py part A compares my Cartesian hub factor with the (delta,H)-chart hub
  part used by the code chain over 300 random points:
     worst |F_cart - F_chart|                 = 5.355e-04
     worst |F_cart - F_chart - (z3-z1)delta|   = 3.666e-16      (z3-z1 = 0.000464943)
  The 5.4e-4 residual is EXACTLY the delta-linear piece of K that the cancellation identity
  absorbs into a1 theta1 + a2 theta2 and which my comparison string omitted; restored, the two
  forms agree to MACHINE ZERO.  So the Cartesian form IS the code objective and the interface is
  sound.  Part B: the analytic gradient (WITH the quadratic terms) vs finite differences of that
  verified objective agrees to 1.2e-10.
2 CORRECTIONS (all three of the lead's, accepted):
  (a) R4 truncation: the correct stationarity is
        alpha + sum_j 2 beta_j L_j n_j = sum_j c_j n_j - sum_j a_j grad theta_j ,
      alpha = (r(1-cosTcosD), -r cosT sinD) being the AFFINE gradient only.  My R4 string omitted
      sum 2 beta_j L_j n_j (~0.6 per component), inconsistent with the 2 beta I in my Hessian.
      The FD-based diagnostics are unaffected (they used the full objective).  Fixed in C862c.
  (b) Scaling: the mixed entry <n, Hess(theta) n^perp> scales as 1/L^2 (times L^2 gives -1 for the
      plain polar angle); my printed "*L = +-1" was dimensionally wrong.  Fixed in C862c.
  (c) Wording: the stationary point with (lambda_min, lambda_max) = (-0.0022, +1.4276) is
      INDEFINITE (lambda_max > 0), not semidefinite; "semidefinite" is withdrawn.  The only
      correct remark is that lambda_min sits near zero, so exclusion may not assume it bounded
      away from 0 from either side.  Fixed in C862c.
  (d) Also recorded in C862b: the two angle terms have OPPOSITE chirality, so that file's Hessian
      (same chirality for both) was a neighbouring function; the corrected re-run in C862c
      supersedes its eigenvalues while the DIRECTION of both conclusions survives.
3 No new numerics beyond the interface check; no claim registered.

================================================================================
ROUND 26 — C868 face-arc vs ridge: reduced mechanism
================================================================================
Deliverable C868-FACE-ARC-MECHANISM.md; instrument tools/face_arc_difference.py; out/p45_face_arc.txt.
Read RIDGE-RANK-ONE-COUPLING.md, face_second_jet.py, FACE-STATIONARY-MAX-COUNTEREXAMPLE.md.
Own files only; no big run; formula-level.

1 EXACT STRUCTURAL IDENTITIES on the face-1 saturated arc (A = b1-delta free, H = 2r sin(b1+A)),
  all three verified symbolically with residual 0:
   (i)   (v,t) = r(sin2b1 + sin2A, cos2A - cos2b1);
   (ii)  L1^2 = |hub - c1|^2 = (2r sinA)^2;
   (iii) sin^2 phi1 = sin^2 b1  =>  the face-1 hub angle is CONSTANT along the arc (numerically
         phi1 = b1), because the face-1 circle is exactly the locus {circumradius = r}.  Hence the
         a1-angle term CANCELS in every difference along the arc - the key simplification.
2 REDUCED ARC OBJECTIVE: G_arc(A) = [area](A) + a1 b1 + a2 phi2(A) + beta1 L1^2 + gamma1 L1
  + beta2 L2^2 + gamma2 L2 + (z3-z1)(b1-A), with [area] AFFINE in (sin2A, cos2A) and L1 = 2r sinA
  elementary; the ridge is the arc point A = b2 (there L1 = 2r sinb2, L2 = 2r sinb1).  So the only
  coupled terms on the arc are a2 phi2 and beta2 L2^2 + gamma2 L2 — exactly the face-2 data.
  Frame check at r=.377, b1=1.008, b2=1.001 (arc constant/width terms dropped, they cancel):
  G_arc(ridge) = -0.480558 vs G_arc at delta = -.320/-.315/-.310 = -0.484664/-0.484662/-0.484671,
  i.e. the certified interior arc maximum sits BELOW the ridge value by ~4.1e-3 — same sign and
  magnitude as the lead's -0.4988 vs -0.4947.
3 THE DIFFERENCE IS AN INTEGRAL and neither monotonicity nor concavity may be assumed (the
  certified arc has an interior local maximum, so G' changes sign at least twice between the
  certified point and the ridge).  Route: handle the affine/elementary part by the RIDGE-RANK-ONE
  chord/tangent linearisation, and treat the residual pair S(A) = a2 phi2 + beta2 L2^2 + gamma2 L2.
4 NEXT OBLIGATION (single scalar inequality): Phi(A) + S(A) <= Phi(b2) + S(b2) for legal A, or the
  weaker endpoint form.  Two in-machinery routes: (a) certify G_arc(A) <= G_ridge by the same
  second-order interval AD as face_second_jet.py, comparing against a CONSTANT; (b) eliminate L2
  and phi2 via the face-2 law of sines (L2/sinB = D2/sin phi2, B affine in A) so S becomes a
  function of one angle with explicit coefficients.
5 LIMITS: section 1 exact; section 2's numbers reproduce the comparison's sign but not absolute
  values (K constant and width terms omitted, harmless for differences); the domination is NOT
  proved — only reduced to the scalar inequality above, with the two obstructions recorded.
