"""R18: source-analytic verification of (1) the stationary Taylor enclosure direction,
(2) the endpoint closure classes, (3) the branch/positivity conditions. No grids, no random loops."""

import math, sys
sys.stdout.reconfigure(encoding='utf-8', errors='replace')

print('=' * 78)
print('(1) stationary Taylor: which sign is sound?')
print('=' * 78)
print("""
Source (probe_stationary_face_bound.py:25-31):
  am = f.saturated(mid, j)           # mid has only coordinate 3 centred
  tight = am.d + am.h*(x[3]-mid[3])  # first-order in delta about mid
  a.d   = [max(a.d.a,tight.a), min(a.d.b,tight.b)]
  centered = am.v - a.h*((x[3]-mid[3])**2)/2
  a.v   = [max(a.v.a,centered.a), min(a.v.b,centered.b)]     # (line 29)
  gate : if a.d.a>0 or a.d.b<0: reject ; if a.h.a>0: reject  (lines 33-34)

Let d* be the stationary point of the delta-component: am = Jet(mid), with
  am.v ~ f(mid),  am.d = f_delta(mid),  am.h = f_deltadelta(mid).
At an isolated local maximum the code requires the derivative enclosure to contain 0
(line 33) so d* exists in x[3], and it requires f_dd <= 0 on the segment (line 34).

Exact second-order Taylor about the stationary point d*:
    f(d*) = f(mid) + f_delta(mid)(d*-mid) + (1/2) f_dd(xi)(d*-mid)^2,
with f_delta(mid) = 0 because d* is stationary IN delta AND f_delta is continuous, so
    f(d*) = f(mid) - (1/2)|f_dd(xi)| (d*-mid)^2        (since f_dd <= 0)
          <= f(mid).
So the true stationary value is at most the midpoint value: the sound enclosure is
    f(d*) <= max(f.v)  and  f(d*) <= f(mid),
i.e. an UPPER bound must ADD the (negative) curvature term, or simply use f(mid).

The code instead computes  centered = f(mid) - (|h|/2)(d*-mid)^2 < f(mid)  and takes
    a.v = [max(a.v.a, centered.a), min(a.v.b, centered.b)].
That is a LOWER-direction correction: it asserts the stationary value is at least
f(mid) - (h/2)(...) - which is the wrong direction for an upper bound. It is sound ONLY if
the second derivative is NONNEGATIVE on the segment (then f(d*) >= centered and the value
is a minimum). But line 34 rejects when a.h.a > 0, i.e. it keeps only boxes with f_dd <= 0 -
exactly the case where the correction is unsound.
""")

r_lo, b_hi = 0.379, math.acos(0.375)
print(f'context: r in [{r_lo}, 0.37999], b in [1, {b_hi:.9f}]')
print('  sign of f_dd is a property of the objective, not of the box: at an interior maximum of a')
print('  1-D slice one ALWAYS has f_dd <= 0, so rejection of a.h.a>0 removes no interior maximum')
print('  while the retained case is exactly the one where line 29 goes the wrong way.')

print()
print('=' * 78)
print('(2) endpoint closure of the legal face arc')
print('=' * 78)
print("""
The face arc is parametrised (face_second_jet.coords) by
    j=0: v = r(sin2b1 + sin2A),  t = r(cos2A - cos2b1),  A = b1-delta
    j=1: v = r(sin2b2 + sin2B),  t = r(cos2B - cos2b2),  B = b2+delta
Every point satisfies |c - c_j| = r identically (c_j the face centre), so the arc lies on its
face circle. Write the three closed constraints as
    g_face_opp  = (|c - c_opp|^2 - r^2) <= 0     (other face circle)
    g_norm      = (|c|^2 - (1-r)^2)     <= 0     (hub norm disk)
    g_wedge     = A >= 0 and B >= 0               (legal(x,j) lines 44-46)
The legal sub-arc is the connected component of the face circle where all g <= 0. An endpoint of
that sub-arc is therefore a point where at least one g is ACTIVE (otherwise a neighbourhood is
still legal). The active constraints are exactly:
    g_face_opp  -> the intersection of the two face circles     (C861)
    g_norm      -> the norm circle |c| = 1-r                    (C863)
    g_wedge     -> A = 0 or B = 0, i.e. a wedge ray             (C861 excludes; H>0 there)
There is no fourth possibility: the arc is closed on its own face circle, and the arc's own
circle is a parametrisation, not a constraint.
=> the three endpoint classes named in the brief (norm C863, ridge C869, C861 wedge/interior
   exclusion) do close the endpoint set, PROVIDED the classes are exactly
   {g_norm active} U {g_face_opp active} U {g_wedge active}. The brief lists "ridge" where the
   natural third class is the wedge ray / opposite-face circle; both are C861/C869 objects, so
   the classification is complete if C869 bounds the ridge (delta = b1-b2) arc with g_norm and
   g_face_opp inactive. That is the one link I could not check from these sources alone:
   certify_ridge_tangent.py bounds the ridge at H = 2r sin(b1+b2) with b1,b2 >= 1, whereas the
   face-arc endpoint at A = 0 sits at H = 2r sin 2b1 - see the note below.
""")
print('  note: at A=0 the arc point is the face centre c_1, whose hub norm is')
for r in (0.379, 0.3799):
    for b in (1.0, 1.18):
        cx = r * math.sin(2 * b); cy = -r * math.cos(2 * b)
        print(f'    r={r} b={b}: |c_1| = {math.hypot(cx, cy):.9f}  1-r = {1-r:.9f}  '
              f'norm-active={abs(math.hypot(cx,cy)-(1-r))<1e-9}')
print('  |c_1| = r != 1-r, so A=0 is a WEDGE endpoint, not a norm endpoint -> C861 class.')

print()
print('=' * 78)
print('(3) branch / positivity conditions in face_second_jet')
print('=' * 78)
print("""
* angle(y,x) raises Unsafe unless y>0 strictly or y<0 strictly or x>0 (line 32) - so the atan2
  branch is [0,pi] with no zero-argument ambiguity. In saturated(), the i!=j call uses
  Y = 2 r sin(b) sin(ang) with b>=1 and ang in (0,pi) => Y > 0 strictly, so the branch is
  always the safe one; the i==j call sets phi = b (no atan2 at all). SOUND.
* sqrt raises Unsafe when the radicand interval touches 0 (line 28), so no derivative is taken
  through a square-root singularity.
* saturated() is a SINGLE formula (line 64-71) evaluated on the whole box: the active phi (=b)
  and the passive phi (=angle) are selected by i==j, which is a branch of the OBJECTIVE, not of
  the interval, so no clipping or branch switching occurs inside a box. This is what "branch
  safe" requires.
* Cartesian agreement: substituting A = b1-delta (j=0) into v,t reproduces the face-circle
  point, and H = 2r sin(2b1-delta) = 2r sin(b1+A) equals the face cap 2r sin(b1+A) used in
  interval_hub_saturated (line 14: H=2r sin(b1+A) for j=0). Same for j=1 with B=b2+delta.
  The (z3-z1)delta term in saturated() is the linear delta coupling; the Cartesian objective
  (face_second_jet.objective) carries the same linear term through J(a)*phi with the phi of the
  active face, d(phi)/d(delta) = -1 for j=0. Consistent.
""")

print()
print('=' * 78)
print('(4) derivative formulas (face_derivative_outer_jet)')
print('=' * 78)
print("""
Line 11:  vd = (-2 if j==0 else 2) r cos(2c),  td = 2r sin(2c)  with c = A (j=0) / B (j=1).
Check j=0: v = r(sin2b1 + sin2A), dv/ddelta = r cos2A * d(2A)/ddelta = r cos2A * (-2).
          t = r(cos2A - cos2b1), dt/ddelta = -r sin2A * (-2) = +2r sin2A.        MATCHES.
Check j=1: v = r(sin2b2 + sin2B), dv/ddelta = 2r cos2B ; t = r(cos2B - cos2b2) -> +2r sin2B
          WITHOUT the extra sign, but line 10 multiplies t by (1 if j==0 else -1) then line 11
          uses td = +2r sin(2c) so dt/ddelta = -2r sin2B.  t = r(cos2B-cos2b2) with B=b2+delta
          gives dt/ddelta = -2r sin2B.  MATCHES (the sign is carried by the t definition).
Line 15:  active face: e = r sin(ang)/R, ed = -/+ r cos(ang)/R, pd = -/+1.
          d e/d delta: for j=0, ang = A, dA/ddelta = -1, so de/ddelta = r cos A/R * (-1). MATCHES.
          pd: phi = b for the active face, dphi/ddelta = 0 in the physical slice but the code
          uses -1/+1 - this is the d(phi)/d(delta) of the ACTIVE FACE ANGLE, consistent with the
          Cartesian phi of that face (line 15 comment "active phi' = +-1"). MATCHES the brief.
Line 16-18: passive face: Q = X^2+Y^2 = 4R^2 e^2, root = 2R e, ed = (X vd + Y sg td)/(2R root)
          = (X vd + Y sg td)/(4R^2 e) = d(sqrt(Q)/(2R))/ddelta. MATCHES the chain rule.
          pd = (X sg td - Y vd)/Q. For a point rotating with (X(t),Y(t)), d/dt atan2(Y,X)
          = (X Y' - Y X')/(X^2+Y^2); the code's numerator is (X * sg*td - Y * vd) and the
          derivative of (X,Y) is (vd, sg*td). MATCHES the generic atan2 derivative.
          Note the brief writes "off e' denom 2R sqrtQ": here sqrtQ = 2R e exactly, so
          ed = (X vd + Y sg td)/(2R * sqrtQ) - the code's (root*2*R) is the same factor. MATCHES.
Line 22-24: enclosure = min of the raw interval value and the MVT linearisation about the
          midpoint with the gradient enclosure f.d. Both are upper bounds, so the minimum is an
          upper bound. No clipping of the derivative path (the Jet carries analytic partials).
""")
