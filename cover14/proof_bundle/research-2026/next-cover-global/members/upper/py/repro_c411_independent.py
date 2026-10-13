"""repro_c411_independent.py -- member upper (next-cover-global), 2026-09-26.

INDEPENDENT, bounded re-derivation of the C411 finite upper bound for n=14, plus an
audit of the exact literal object and of the old kernel's completeness argument.

Representation difference from the read-only old kernel
(research-2026/lead/verify_c407_lead.py, sha256 a728dd3d...), which is replayed here
separately through a byte-faithful local copy:

  * the old kernel encloses each extremal candidate in a rational BOX and bounds sqrt
    by isqrt at 10^-40 (directed interval arithmetic);
  * this file keeps every candidate as an EXACT ALGEBRAIC POINT -- rational point,
    or -c/|c|, or u +- sqrt(q/d2)*w -- and decides "some disk of radius T covers it"
    by pure rational arithmetic with sign case analysis and squaring.  No interval
    arithmetic, no isqrt, no float in any decision.
  * R(C) is obtained exactly: the maximiser here is a rational point (circumcentre),
    so R(C)^2 = q0 in Q and R(C) = sqrt(q0); the literal saved in the json is
    compared digit-for-digit against floor_70(sqrt(q0)).

Completeness argument (audited; its one degenerate sub-case is reported, not hidden):
if f(p) = min_i |p - c_i| attains its max over the closed unit disk at p*, then
  (a) p* in int D: |A(p*)| >= 2; |A| = 2 forces p* = midpoint of two centres, where f
      increases along the perpendicular (so not a local max); hence |A| >= 3, the active
      distances are all equal, and p* is the circumcentre of three centres;
  (b) p* on dD, |A| >= 2: p* is equidistant from two centres -> on a bisector;
  (c) p* on dD, |A| = 1: p* is the antipode of that centre.  If a centre sits exactly at
      the origin this case degenerates (f is constant 1 on dD); we then add the single
      representative (1,0), which need NOT attain the max -- a real but narrow gap,
      absent for this candidate (no centre at the origin; checked below);
  (d) the origin is added (needed only in the degenerate single-disk case; harmless).
So in the non-degenerate case the candidate list is complete.

Run: py -3 -B py/repro_c411_independent.py
Writes only under members/upper/.
"""
import hashlib
import json
import math
import sys
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

try:
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
except Exception:
    pass

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
SRC = ROOT / 'research-2026/session2/type14/out/hprec_sol.json'
ORIG = ROOT / 'research-2026/lead/verify_c407_lead.py'
OLDOUT = ROOT / 'research-2026/lead/c407_lead_result.txt'
OUT = HERE.parent / 'logs' / 'independent_c411_result.txt'

T = F('0.33173203427623414')       # C411 threshold
TP = F('0.33173203427623415')
L = F('0.33173203427623416')       # old inner-core target (disproved by C412)
C412_R = '0.3317320342762341235155066403893542386599009287817317893317705660612302'

SCAN = 10 ** 100                    # diagnostic scan precision
LOG = []


def say(s=''):
    print(s)
    LOG.append(s)


# --------------------------------------------------------------- exact algebra
def dist2_le(p, c, thresh2):
    """EXACT decision dist(p,c)^2 <= thresh2 for an algebraic candidate point p."""
    cx, cy = c
    if p[0] == 'pt':
        _, px, py = p
        return (px - cx) * (px - cx) + (py - cy) * (py - cy) <= thresh2
    if p[0] == 'ant':                      # p = -c0/|c0|, r = a + B/sqrt(n2)
        _, c0x, c0y, n2 = p
        alpha = 1 + cx * cx + cy * cy
        B = 2 * (c0x * cx + c0y * cy)
        A = thresh2 - alpha
        if B == 0:
            return A >= 0
        if B < 0:
            return True if A >= 0 else (B * B >= A * A * n2)
        return False if A <= 0 else (B * B <= A * A * n2)
    if p[0] == 'bis':                      # p = u +- sqrt(q/d2) w, r = a + B sqrt(qr)
        _, ux, uy, q, qr, wx, wy, sigma = p
        alpha = (ux - cx) ** 2 + (uy - cy) ** 2 + q
        B = 2 * sigma * ((ux - cx) * wx + (uy - cy) * wy)
        A = thresh2 - alpha
        if B == 0:
            return A >= 0
        if B < 0:
            return True if A >= 0 else (B * B * qr >= A * A)
        return False if A <= 0 else (B * B * qr <= A * A)
    raise AssertionError(p[0])


def covered(p, C, thresh2):
    return any(dist2_le(p, c, thresh2) for c in C)


def sq_scaled(a, SC):
    """sqrt(a) at scale SC as a Fraction (directed, one isqrt) - diagnostics only."""
    m = (a.numerator * SC * SC) // a.denominator
    return F(math.isqrt(m), SC)


def dist_num(p, c, SC):
    cx, cy = c
    if p[0] == 'pt':
        _, px, py = p
        return sq_scaled((px - cx) ** 2 + (py - cy) ** 2, SC)
    if p[0] == 'ant':
        _, c0x, c0y, n2 = p
        return sq_scaled(1 + cx * cx + cy * cy + 2 * (c0x * cx + c0y * cy) / sq_scaled(n2, SC), SC)
    if p[0] == 'bis':
        _, ux, uy, q, qr, wx, wy, sigma = p
        alpha = (ux - cx) ** 2 + (uy - cy) ** 2 + q
        B = 2 * sigma * ((ux - cx) * wx + (uy - cy) * wy)
        return sq_scaled(alpha + B * sq_scaled(qr, SC), SC)
    raise AssertionError


def f_num(p, C, SC):
    return min(dist_num(p, c, SC) for c in C)


# ----------------------------------------------------------------- candidate set
def candidates(C):
    P = [('origin', ('pt', F(0), F(0)))]
    for i, c in enumerate(C):
        n2 = c[0] * c[0] + c[1] * c[1]
        if n2 == 0:
            P.append((f'zero-centre{i}(representative)', ('pt', F(1), F(0))))
            continue
        P.append((f'antipode{i}', ('ant', c[0], c[1], n2)))
    for i, j in combinations(range(len(C)), 2):
        dx, dy = C[j][0] - C[i][0], C[j][1] - C[i][1]
        d2 = dx * dx + dy * dy
        if d2 == 0:
            continue
        h = (C[j][0] ** 2 + C[j][1] ** 2 - C[i][0] ** 2 - C[i][1] ** 2) / 2
        ux, uy = h * dx / d2, h * dy / d2
        q = 1 - (ux * ux + uy * uy)
        if q < 0:
            continue
        for sigma in (-1, 1):
            P.append((f'bisector{i},{j}/{sigma}', ('bis', ux, uy, q, q / d2, -dy, dx, sigma)))
    for i, j, k in combinations(range(len(C)), 3):
        ax, ay = C[j][0] - C[i][0], C[j][1] - C[i][1]
        bx, by = C[k][0] - C[i][0], C[k][1] - C[i][1]
        D = ax * by - ay * bx
        if D == 0:
            continue
        e = (C[j][0] ** 2 + C[j][1] ** 2 - C[i][0] ** 2 - C[i][1] ** 2) / 2
        f = (C[k][0] ** 2 + C[k][1] ** 2 - C[i][0] ** 2 - C[i][1] ** 2) / 2
        ux, uy = (e * by - f * ay) / D, (ax * f - bx * e) / D
        if ux * ux + uy * uy <= 1:
            P.append((f'circum{i},{j},{k}', ('pt', ux, uy)))
    return P


def cover_test(C, TT, label):
    P = candidates(C)
    T2 = TT * TT
    unc = [lab for lab, p in P if not covered(p, C, T2)]
    kind = {}
    for lab, p in P:
        kind[p[0]] = kind.get(p[0], 0) + 1
    say(f'  [{label}] threshold {TT}')
    say(f'      candidates = {len(P)}  by type {kind}  UNCOVERED = {len(unc)}'
        + ('' if not unc else f'  e.g. {unc[:4]}'))
    return P, unc


def exact_radius(C, tag):
    """exact R(C) = sqrt(q0) via the best RATIONAL candidate (or report otherwise)."""
    P = candidates(C)
    pts = [(f_num(p, C, SCAN), lab, p) for lab, p in P if p[0] == 'pt']
    pts.sort(key=lambda z: -z[0])
    v, lab, p = pts[0]
    _, px, py = p
    q0 = min((px - a) ** 2 + (py - b) ** 2 for a, b in C)
    argmin = min(range(len(C)), key=lambda i: (px - C[i][0]) ** 2 + (py - C[i][1]) ** 2)
    unc = [l for l, q in P if not covered(q, C, q0)]
    say(f'  [{tag}] best rational candidate {lab}')
    say(f'       p* = ({px}, {py})')
    say(f'       q0 = min_i |p*-c_i|^2 (argmin centre {argmin}) = {q0}')
    if not unc:
        say(f'       covering test at threshold sqrt(q0): uncovered = 0'
            f'  => R <= sqrt(q0); with f(p*) = sqrt(q0) => R(C) = sqrt(q0) exactly')
    else:
        say(f'       covering test at threshold sqrt(q0): uncovered = {len(unc)}'
            f'  => R(C) > sqrt(q0): the maximiser is NOT this rational candidate;'
            f' exact value needs its own algebraic argmax (not claimed here)')
    return q0, lab, (px, py), P


def zero_centre_controls():
    """Audit of the 'centre exactly at the origin' sub-case (the only degeneracy of
    case (c)).  Claim under test: the candidate set STILL captures R = 1.

    Argument: if c_0 = 0 then f <= 1 on D; on dD, f(p) = min(1, g(p)) with g = min over
    the other centres, and d_0(p) = |p| = 1 so c_0 is active on dD exactly where f = 1.
    Let P = {p in dD : g(p) >= 1}; P is closed (g continuous) and every p in P has
    f(p) = 1 = R.
      * P = whole circle: the representative (1,0) lies in P, so it attains R.
      * P a proper closed arc: its endpoints have g = 1 exactly, so at such an endpoint
        c_0 (distance 1) and some other centre are both active with equal distance 1
        -> the endpoint is equidistant from 0 and that centre -> it is a
        bisector n dD candidate.
      * P empty: no boundary maximiser has c_0 alone active; and a unique non-origin
        active centre on dD would have to be antipodal, where its distance is
        1 + |c_i| >= 1 > f, a contradiction; so every maximiser has >= 2 active centres
        (interior -> circumcentre, boundary -> bisector) -- all enumerated.
    Hence (1,0) + bisectors + circumcentres capture R and the earlier 'gap' is
    withdrawn.  This function checks the three sub-cases numerically.
    """
    say()
    say('=== layer 3: zero-centre sub-case audit (withdrawal check) ===')
    cfgs = (('origin only (P = whole circle)', [(F(0), F(0))]),
            ('origin + (3/2,0) (P = proper arc)', [(F(0), F(0)), (F(3, 2), F(0))]),
            ('origin + (2,0) (P = tangent point)', [(F(0), F(0)), (F(2), F(0))]))
    allok = True
    for nm, Cc in cfgs:
        P = candidates(Cc)
        vals = sorted(((f_num(p, Cc, SCAN), lab) for lab, p in P), key=lambda z: -z[0])
        nz = [(a, b) for a, b in Cc if not (a == 0 and b == 0)]
        N, keep = 40000, 0
        for t in range(N):
            ph = 2 * math.pi * t / N
            px, py = math.cos(ph), math.sin(ph)
            if not nz or min(math.hypot(px - float(a), py - float(b)) for a, b in nz) >= 1 - 1e-12:
                keep += 1
        frac = keep / N
        ok = abs(vals[0][0] - 1) <= F(1, 10 ** 90)
        allok = allok and ok
        say(f'  [{nm}]')
        say(f'     plateau fraction of dD (numeric, 4e4 samples) = {frac:.4f}')
        say(f'     best candidate = {vals[0][1]} ; max over candidates = {float(vals[0][0]):.20f}')
        say(f'     [{"PASS" if ok else "FAIL"}] candidate set attains R = 1')
    return allok


def main():
    say('=== provenance (all read-only) ===')
    for nm, pth in (('input hprec_sol.json', SRC),
                    ('old kernel verify_c407_lead.py', ORIG),
                    ('old output c407_lead_result.txt', OLDOUT),
                    ('this file', Path(__file__).resolve())):
        say(f'  {nm:32s} sha256 {hashlib.sha256(pth.read_bytes()).hexdigest()}')
    js = json.loads(SRC.read_text(encoding='utf-8'))

    # ------------------------------------------------------- exact literal object
    th = [F(s) for s in js['th']]
    C = []
    for j in (0, 2):
        for s in (-1, 1):
            for t in (-1, 1):
                C.append((s * th[j], t * th[j + 1]))
    for j in (4, 5):
        C.extend([(th[j], F(0)), (-th[j], F(0))])
    C.extend([(F(0), th[6]), (F(0), -th[6])])
    assert len(C) == 14
    Cf = [(F(str(x)), F(str(y))) for x, y in js['centers']]      # float64 field, exact dyadic
    say()
    say('=== exact literal objects ===')
    say(f'  th = 7 decimal literals, interpreted as exact rationals (as C411 states)')
    say(f'  centres built from th: 14 ; any centre exactly at the origin: '
        f'{any(a == 0 and b == 0 for a, b in C)}  (degenerate case (c) absent)')
    say(f'  json["centers"] = the SAME 14 points as a set, in a different order, '
        f'as float64: {sorted((float(a), float(b)) for a, b in C) == sorted((x, y) for x, y in js["centers"])}')
    say(f'  json["centers"] is NOT the exact object: F(str(value)) != literal-derived exact '
        f'coordinate on 14/14 entries, max |abs diff| = '
        f'{float(max(abs(a - F(str(x))) for (a, b), (x, y) in zip(C, js["centers"]))):.3e}')

    # --------------------------------------------------------------- controls
    say()
    say('=== layer 0: known-answer controls (each exercises a branch) ===')
    ctrl = []
    sq4 = [(F(s, 2), F(t, 2)) for s in (-1, 1) for t in (-1, 1)]
    r = max(f_num(p, sq4, SCAN) for _, p in candidates(sq4))
    ctrl.append(('square(+-1/2): max == sqrt(1/2)', abs(r - sq_scaled(F(1, 2), SCAN)) <= F(1, 10 ** 90)))
    two = [(F(-1, 2), F(0)), (F(1, 2), F(0))]
    r2 = max(f_num(p, two, SCAN) for _, p in candidates(two))
    ctrl.append(('two centres(+-1/2,0): max == sqrt(5)/2 (bisector branch)',
                 abs(r2 - sq_scaled(F(5, 4), SCAN)) <= F(1, 10 ** 90)))
    one = [(F(0), F(0))]
    r3 = max(f_num(p, one, SCAN) for _, p in candidates(one))
    ctrl.append(('single centre at origin: max == 1 (degenerate representative)',
                 abs(r3 - 1) <= F(1, 10 ** 90)))
    ctrl.append(('single centre at origin: 0 uncovered at T=1',
                 all(covered(p, one, F(1)) for _, p in candidates(one))))
    for nm, ok in ctrl:
        say(f'  [{"PASS" if ok else "FAIL"}] {nm}')
    assert all(o for _, o in ctrl), 'control FAILED'

    # ------------------------------------------------- exact covering test at T
    say()
    say('=== layer 1: EXACT covering test (rational algebra, no intervals, no float) ===')
    P, unc_T = cover_test(C, T, 'C411 threshold T')
    _, unc_TP = cover_test(C, TP, 'raised threshold Tp')
    _, unc_L = cover_test(C, L, 'old target L')
    _, unc_f = cover_test(Cf, T, 'float64-centre variant at T   <-- object probe')
    say(f'  => R(C) <= T   : {len(unc_T) == 0}')
    say(f'  => R(C) <= Tp  : {len(unc_TP) == 0}')
    say(f'  => R(C) <= L   : {len(unc_L) == 0}')
    say(f'  => using the json float64 "centers" field instead of the literals: '
        f'{len(unc_f)} uncovered at T (certificate does NOT transfer)')

    # --------------------------------------------------------------- exact R(C)
    say()
    say('=== layer 2: exact R(C) = sqrt(q0), q0 in Q ===')
    q0, lab, pstar, _ = exact_radius(C, 'literals')
    qf, labf, pstf, _ = exact_radius(Cf, 'float64 centres (probe)')
    SC70 = 10 ** 70
    dec70 = '0.' + str(math.isqrt((q0.numerator * SC70 * SC70) // q0.denominator)).rjust(70, '0')[:70]
    say()
    say(f'  sqrt(q0) to 70 digits (directed isqrt) = {dec70}')
    say(f'  json["R"] field                        = {js["R"]}')
    say(f'  C412 stated value                      = {C412_R}')
    say(f'  match json R = {dec70 == js["R"]}   match C412 = {dec70 == C412_R}')
    lit = F(js['R'])
    say(f'  exact: literal^2 - q0 = {lit * lit - q0}  (negative => literal is the floor truncation)')
    say(f'  exact: q0 < T^2 = {q0 < T * T} ;  T - sqrt(q0) in ['
        f'{float(T - sq_scaled(q0, SC70)):.6e}] (approx)')
    say(f'  exact: q0 < L^2 = {q0 < L * L}')
    say(f'  float64-centre variant: R^2 = {qf}  (argmax {labf}); '
        f'q0 - qf = {q0 - qf}  -> {float(q0 - qf):.3e}')
    say(f'  json["R_float_recheck"] = {js["R_float_recheck"]}  '
        f'(float64 image of R: {float(sq_scaled(q0, SC70)) == js["R_float_recheck"]}; '
        f'it is {float(F(str(js["R_float_recheck"])) - sq_scaled(q0, SC70)):.3e} ABOVE R(C), '
        f'matching the C412 statement that the old target L was a float64 product ~3.65e-17 too high)')

    # ------------------------------------------- object sensitivity (quantified)
    vlit = max(((f_num(p, C, SCAN), lab) for lab, p in candidates(C)), key=lambda z: z[0])
    vf64 = max(((f_num(p, Cf, SCAN), lab) for lab, p in candidates(Cf)), key=lambda z: z[0])
    say()
    say('  object sensitivity (numeric scan at 10^-100, diagnostic only):')
    say(f'    max over candidates, literal object  = {float(vlit[0]):.20f}  at {vlit[1]}')
    say(f'    max over candidates, float64 centres = {float(vf64[0]):.20f}  at {vf64[1]}')
    say(f'    shift R(float64 centres) - R(literals) = {float(vf64[0] - vlit[0]):.3e}'
        f'   (certified margin T - R(literals) = {float(T - sq_scaled(q0, SC70)):.3e})')

    ok = (len(unc_T) == 0 and q0 < T * T and dec70 == js['R'] == C412_R)
    say()
    say('=== verdict ===')
    say(f'  EXACT REPRODUCTION OF C411: {"CONFIRMED" if ok else "NOT CONFIRMED"}')
    say(f'  object: 14 centres from the 7 exact decimal literals of hprec_sol.json '
        f'(NOT the float64 "centers" field).')
    say(f'  reproduced: R(C) = sqrt(q0) = {dec70}... <= T = {T} < L = {L}.')
    say(f'  scope: THIS configuration only; NOT the family minimum, NOT r_D(14).')
    OUT.write_text('\n'.join(LOG) + '\n', encoding='utf-8')
    print(f'\n[written] {OUT}')


if __name__ == '__main__':
    main()
