# Independent audit: K10-HUB-LINE-CHART.md and K10-NEAR-MERGE-REDUCTION.md

Auditor: structure member. Read-only on lead files. Evidence dir:
`research-2026/n12-global/members/structure/hub-line-audit/`.
Script: `check_core_criterion.py` (constructed algebraic cases + labelled
secondary sanity scan; the *verification* is the algebra below, not sampling).

Constants: U = 0.361102963744508672616920293904, a = 1-2U = 0.277794072510983,
e0 = 3U-1 = 0.083308891233526, d = 2s.

## Verdict summary

| item | verdict |
|---|---|
| full-domain charts h1=(x-s,y), h2=(x+s,y), x,y>=0 | OK (with the two caveats in A) |
| exposed arcs centred at 0 and pi, halfwidth pi-acos(s/U) | OK (derivation in B) |
| exact core criterion (cases x>=a / 0<=x<a + guarded antipode) | OK, no arc maximum is missed (C) |
| uniform bounds y<=e0 and x<=s+e0 | OK (D) |
| s<U in the "containing box" | the bound s<=U is TRUE but needs the proof in D; the box must be (0,U], not (0,U) — s=U is attained exactly |
| near-merge containing disc, e<=3U-1+delta, int D condition | OK |
| near-merge closedness at tangency points | OK (limiting argument verified exactly, F) |
| near-merge capture half-width uses ell=|c-h1| | FLAG: the target circle is centred at m, so ell must be |c-m| (F) |

## A. Is the three-parameter chart full-domain?

Yes. Rotation (a Euclidean isometry, preserves the covering problem and both
radii) puts h2-h1 horizontal; then h1=(x-s,y), h2=(x+s,y) with s=d/2>0.
Reflection in the y-axis is an isometry preserving the problem; combined with
swapping the two hub labels it replaces x by -x, so x>=0 is WLOG; reflection in
the x-axis replaces y by -y, so y>=0 is WLOG. The ring discs are untouched by
the label swap. Caveats:
 (i) d=0 (coincident hubs) is not representable (s>0); it is delegated to the
     near-merge document, which handles d<=2delta. Together the two cover all
     d>0 (with an overlap for 0<d<=2delta), provided the near-merge delta is
     certified.
 (ii) "inactive constraints are (x+s)^2+y^2<=(1-U)^2 (the other follows)": true
     because the inactive condition for h_j is |h_j|<1-U and |x-s|<=x+s for
     x,s>=0, so the h2 inequality implies the h1 one. Equality (|h_j| = 1-U)
     must be kept as a limit case: the hubs are then boundary-active, i.e. the
     configuration belongs to the other k-class, so for the k=10 branch one may
     impose |h_j|<1-U and pass to the closed constraint only by an enlargement
     argument; the document leaves this to the caller.

## B. Exposed arcs

The two circles S(h1,U), S(h2,U) meet (for s<U) where |X-h2|=|X-h1| and
|X-h2|=U, i.e. at the bisector points. Subtracting the two equations gives
X = x (bisector), and then |(X-h2)|^2 = (X-x-s)^2+(Y-y)^2 = U^2, so the two
points are (x, y +- sqrt(U^2-s^2)). Relative to h2 the vectors to them are
(-s, +-sqrt(U^2-s^2)), of length U, so their direction cosines from the +x axis
are -s/U, i.e. their angles are +-(pi - acos(s/U)). Hence the part of
S(h2,U) outside B(h1,U) is the arc centred on direction 0 with halfwidth
pi - acos(s/U); symmetrically for h1 on direction pi. This matches the
document. Note for the ring: the exposed-arc halfwidth does not depend on x,y,
which is why "all branch directions fixed" is a legitimate claim.

## C. The exact core criterion is correct (no missed arc maximum)

Independent re-derivation. Let K=B(0,a), f(X)=min_j|X-h_j|.
 f(X)^2 difference: |X-h1|^2-|X-h2|^2 = 4s(X_1-x), so h1 is the nearest hub
 exactly on {X_1<=x}. Hence dK splits into the arc A1={X in dK: X_1<=x} (h1
 nearest) and A2={X in dK: X_1>=x} (h2 nearest).
 (1) max_K f is attained on dK. If a maximiser X had |X-h1| != |X-h2| then
     moving X slightly away from the (strictly) nearest hub increases the
     relevant distance and does not affect the other one, contradicting
     maximality. If |X-h1|=|X-h2| then X lies on the bisector and moving along
     the bisector away from (h1+h2)/2 increases both distances by the same
     amount (both equal sqrt(s^2+t^2) with |t| the bisector offset), again a
     contradiction unless X is on the boundary. For h1=h2 the maximiser is
     again on dK (f(X)=|X-h|). So the criterion "max over dK <= U" is exact.
 (2) On the circle dK, |X-h|^2 = a^2 - 2a(X_1 h_1 + X_2 h_2)/a + |h|^2, whose
     stationary points are X = +-a*h/|h|: the *maximum* of |X-h| on dK over the
     whole circle is at X = -a h/|h| (= "the antipode"), the minimum at +a h/|h|.
     Therefore on an arc the maximum of the distance to the arc's own hub is at
     an arc endpoint or (if it belongs to the arc) at that hub's antipode; any
     other stationary point is a minimum and cannot be the required maximum.
     This is exactly the document's statement, and it is complete: the
     antipode of h2 lies at X_1 = -a(x+s)/|h2| < 0 <= x, hence outside A2
     (which requires X_1>=x); so A2 contributes only its endpoints. A1
     contributes its endpoints plus the antipode of h1 when
     -a(x-s)/|h1| <= x  <=>  a(s-x) <= x|h1| (the guard; automatic when
     s<=x since the left side is <=0).
 (3) Endpoint values: at (x, +-q) with q=sqrt(a^2-x^2) both hubs are equidistant
     and the common value is s^2+(y-+q)^2, whose maximum over the two points is
     s^2+(y+q)^2; the covering requires it <= U^2 (and then the other value
     automatically satisfies it). The antipodal value is a+|h1|, so the guarded
     condition is a+|h1|<=U <=> |h1|<=U-a=e0.
 (4) Case x>=a: q is imaginary, dK=A1 entirely, and the maximum of f on dK is
     the maximum of |X-h1| = a+|h1| at the antipode; condition |h1|<=e0. The
     document states exactly this. Note the endpoints condition is vacuous here,
     and no other maximum exists.
Squaring the guard: for s>x it is a^2(s-x)^2 <= x^2((x-s)^2+y^2) (both sides
non-negative), matching the document; for s<=x it holds without any condition.
Sufficiency and necessity hold including equality cases (at equality the
corresponding boundary point is at distance exactly U, which is allowed since
the discs are closed).

Verification artifact: `check_core_criterion.py` evaluates the maximum of f over
dK independently, at the complete candidate list (endpoints, both antipodes with
their arc-membership guards), and compares with the document's criterion:
10 algebraically constructed cases (case boundary, guard boundary s=x, tangency,
x=0, s just below U, infeasible large s) all agree, and the two exact-rational
identities U-a = e0 and |h1|+a = U at (s,x,y)=(U,a,0) hold to 0.0. A secondary
random scan (labelled, not the verification) shows 0 disagreements.

## D. Uniform bounds: correct, and s<=U needs one extra proof

(D1) Core point (-a,0) (X_1=-a<=x, so h1 is nearest): |(-a,0)-h1|^2 =
     (a+x-s)^2+y^2 <= U^2, hence x <= s+U-a = s+e0. Correct.
(D2) y-axis points (0,+-a): the nearest distances are (x-s)^2+(a-+y)^2 (as
     |x-s|<=x+s), so (x-s)^2+(a+y)^2<=U^2. Correct, and it gives
     0<=y<=sqrt(U^2-(x-s)^2)-a <= U-a = e0. Correct.
(D3) NEW, and needed for the "containing box" claim s<U:
      case x>=a: inactivity gives (x+s)^2+y^2<=(1-U)^2, so x+s<=1-U; with
        x>=a this yields s <= 1-U-a = U.
      case 0<=x<a: the endpoints condition s^2+(y+q)^2<=U^2 gives s<=U at once.
     So s<=U always; equality forces (case 1) x=a, y=0, s=U, i.e.
     h1=(-e0,0), h2=(1-U,0), which is an exact-rational boundary configuration
     (|h1|+a=U and |h2|=1-U, so both hubs are tangent to the core and to S^1
     respectively). Therefore the box written as s in (0,U) should be s in
     (0,U]; dropping the endpoint loses a legal limit configuration, which
     matters for a certificate even though it is measure zero.
(D4) NEW lower bound, case x>=a only: |x-s|<=e0 together with x>=a gives
     s >= a-e0 = 2-5U = 0.194486... This is compatible with (and much stronger
     than) the near-merge's intended restriction s>=1/20.

## E. Usable reductions derived here

R1. If s<=x then |h1|<=e0 is required (no case split): for x>=a this is C(4);
    for x<a the guard holds automatically, so C(3) requires it.
    Equivalently: s<=x  =>  (x-s)^2+y^2 <= e0^2.
R2. If x<a then s^2+(y+q)^2 <= U^2, hence s<=U, y<=e0 and (x-s)^2+y^2 <= U^2 - 
    hmm: more precisely the endpoint condition, the guard condition (when
    s>x), and R1 when s<=x, exhaust the core requirement.
R3. If x>=a then s>=2-5U, |x-s|<=e0 and y<=e0; in particular the near-merge
    regime s<=1/20 cannot occur in case x>=a.
R4. s<=U in all cases with the single equality point above.
These reduce the core domain to
    case 1: x>=a, s in [2-5U, U], y in [0,e0], x in [a, min(s+e0, 1-U-s)];
    case 2: 0<=x<a, s^2+(y+q)^2<=U^2 (q=sqrt(a^2-x^2)), plus |h1|<=e0 whenever
            s<=x or a(s-x)<=x|h1|,
and the inactivity (x+s)^2+y^2<=(1-U)^2 throughout.

## F. Near-merge reduction

(F1) B(h1,U) u B(h2,U) c B(m,U+d/2) c B(m,U+delta): correct (triangle
     inequality, |h_j-m|=d/2<=delta).
(F2) Core covered => B(0,a) c B(m,U+delta) => e=|m| <= U+delta-a = 3U-1+delta.
     Correct.
(F3) |m|+U+delta <= 4U-1+2delta < 1 => the containing disc lies in int D.
     Correct.
(F4) Closedness at the outer circle S(m,R), R=U+delta. For X in S(m,R):
     |X-h_j|^2 = R^2+(d/2)^2 - 2(X-m).(m-h_j) >= (R-d/2)^2 >= U^2, with
     equality only if d=2delta and X-m is parallel to m-h_j. In the generic
     case both distances exceed U, so X is outside both closed hubs. At the
     equality point the two distances are exactly U; moving from X in the
     direction X-m (radially outward from m) gives |X+tu-h_j| = U+t for both
     j (exact computation: X-h_j is parallel to X-m there, and X-h_k =
     (R-d/2)u with u=(m-h_j)/|m-h_j|), and small t keeps the point inside D
     because of (F3). Hence every point of S(m,R) is a limit of points of D
     outside both closed hubs, and since the ten ring discs are closed and must
     contain those points, S(m,R) is covered by the ten ring discs. The
     document's claim is therefore correct; the argument does need this
     perturbation step at the tangency points.
(F5) The ring discs also cover S^1 because both hubs are inactive
     (|h_j|+U<1). Correct.
(F6) FLAG. The capture half-width for the target circle S(m,R) is
        beta = acos((R^2 + l^2 - U^2)/(2 R l)),  l = |c - m|,
     since the circle is centred at m. The document writes l=|c-h1|. The two
     coincide only at delta=0 (where h1=h2=m). Since beta is NOT monotone with
     a controlled sign in l (it rises from 0 at l=R-U to arcsin(U/R) at
     l=sqrt(R^2-U^2), then falls to 0 at l=R+U, with unbounded slope near both
     ends), substituting |c-h1| is not automatically conservative. The fix is
     local: use |c-m|; the document's other bounds survive verbatim because
     |c-m| >= |c| - |m| >= (1-U) - (3U-1+delta) = 2-4U-delta as well, which also
     excludes the branch l<=R-U for small delta, and l+R<=U is impossible since
     R>U. After the fix the "same K1 nonnegative-measure dual with denominator
     10" statement is sound.
(F7) The divisor change from 11 to 10 is legitimate only after (F4): both
     target circles are covered by the ten ring discs alone, and the two hubs
     contribute no arc to either circle (on S^1 they are inactive; on S(m,R)
     they capture at most the tangency points, which are limits of points they
     miss, so no positive-measure arc). If one insists on arc functionals, the
     hub contributions must be added to the rows rather than dropped.

## G. Scope of this audit

Proved here by independent algebra: A, B, C, D1-D4, E, F1-F5, F7; flagged as
needing a fix: the box endpoint s=U (D3) and the ell definition (F6).
Not audited: the interval kernels themselves, the existence of a positive
delta in the near-merge, and anything about k=9 or the final optimal radius.
No sampling is used as evidence; the random scan in
`check_core_criterion.py` is labelled secondary.
