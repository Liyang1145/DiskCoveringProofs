"""r20-geometry Round-9: tight 3-disk witness candidates at the certified candidate (central fiber).

At a = hub A (cert 2), b = hub B (cert 0), the central constraints are tight (R_{c_0}=R_{c_4}=r), so by
the lead's fiber theorem b lies on the two central disks' boundaries; 3 of the 5 fan-B pins are also
saturated at b.  For every triple among {central disk 0, central disk 1, fan-B pins} we report:
  * psi = MEC radius of the three centres (longest/2 if obtuse/right/collinear, else circumradius)
  * singleton test: the three disks' intersection is {b} iff the three normals (b-centre)/r do not lie
    in an open half-plane (max cyclic angular gap <= pi)
  * the two tight triples (psi = r to rounding) are the candidate "tight witnesses" whose analytic
    non-sharpness is discussed in GLOBAL-PARAMETER-COUNT-AND-COVERAGE.md.
No grid, no claim.  Repro: py -3 -B -X utf8 research-2026/team-current/r20-geometry/central_tight_triple.py
"""
import io, json, itertools
from mpmath import mp, mpf, sqrt, acos, cos, sin, atan2, pi as MP_PI
from pathlib import Path

mp.dps = 45
HERE = Path(__file__).resolve().parent
ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s)


OBJ = json.load(io.open(ROOT / "n11/upper/certified_object.json", encoding="utf-8"))
SC = mpf(10) ** int(OBJ["decimals"])
C = [(mpf(int(a)) / SC, mpf(int(b)) / SC) for a, b in OBJ["centers_scaled_1e17"]]
R = mpf(OBJ["certified_interval"]["lo"])
RHO = 1 - R
HA, HB = C[2], C[0]                      # a = hub A, b = hub B
CA, CB = C[5], C[6]                      # central sites (lead 0, 4)
FANB = [(6, 4), (4, 9), (9, 10), (10, 3), (3, 5)]


def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def add(p, q):
    return (p[0] + q[0], p[1] + q[1])


def mul(s, p):
    return (s * p[0], s * p[1])


def nrm(p):
    return sqrt(p[0] ** 2 + p[1] ** 2)


def dot(p, q):
    return p[0] * q[0] + p[1] * q[1]


def roots(a, c, r):
    m = mul(mpf(1) / 2, add(a, c))
    dv = sub(c, a)
    d = nrm(dv)
    if d == 0 or d > 2 * r:
        return None
    n = (-dv[1] / d, dv[0] / d)
    k = sqrt(r * r - d * d / 4)
    return (sub(m, mul(k, n)), add(m, mul(k, n)))


def pin(i, j, r):
    p = roots(C[i], C[j], r)
    if p is None:
        return None
    return p[0] if nrm(p[0]) < nrm(p[1]) else p[1]


def mec(pts):
    (A, B, Cc) = pts
    a2 = dot(sub(B, Cc), sub(B, Cc))
    b2 = dot(sub(Cc, A), sub(Cc, A))
    c2 = dot(sub(A, B), sub(A, B))
    ip = [dot(sub(B, A), sub(Cc, A)), dot(sub(A, B), sub(Cc, B)), dot(sub(A, Cc), sub(B, Cc))]
    if min(ip) <= 0:
        return sqrt(max(a2, b2, c2)) / 2, "diameter"
    al = a2 * (b2 + c2 - a2)
    be = b2 * (c2 + a2 - b2)
    ga = c2 * (a2 + b2 - c2)
    cen = mul(1 / (al + be + ga), add(add(mul(al, A), mul(be, B)), mul(ga, Cc)))
    return nrm(sub(cen, A)), "circumcircle"


def inward_and_gaps(b, centres, r):
    """At b on all three boundaries (|b-q_i| = r), a direction v is admissible (b+s v stays in all
    disks for small s>0) iff v.(q_i - b) > 0 for every i.  Hence:
       max cyclic angular gap <= pi  <=>  the normals (q_i-b) do NOT fit in an open half-plane
                                     <=>  NO common strict inward direction  <=>  intersection = {b}
       max gap > pi                  <=>  some open half-plane contains all normals
                                     <=>  a common strict inward direction exists  <=>  interior.
    (This is the correction of the earlier note text, which quoted 189 deg from a different run.)"""
    dirs = [sub(q, b) for q in centres]          # normals q_i - b
    angs = sorted([atan2(d[1], d[0]) for d in dirs])
    n = len(angs)
    gaps = []
    for i in range(n):
        nxt = angs[i + 1] if i + 1 < n else angs[0] + 2 * MP_PI
        gaps.append(nxt - angs[i])
    gmax = max(gaps)
    return (gmax <= MP_PI), [float(g * 180 / MP_PI) for g in gaps]


def bary_weights(pts):
    """barycentric weights of the circumcentre (positive <=> acute, centre inside)."""
    (A, B, Cc) = pts
    a2 = dot(sub(B, Cc), sub(B, Cc))
    b2 = dot(sub(Cc, A), sub(Cc, A))
    c2 = dot(sub(A, B), sub(A, B))
    al = a2 * (b2 + c2 - a2)
    be = b2 * (c2 + a2 - b2)
    ga = c2 * (a2 + b2 - c2)
    s = al + be + ga
    return (al / s, be / s, ga / s)


say("CALIBRATION (lead): MEC of (0,0),(2,0),(1,0.05) must be the diameter 1, NOT the circumradius")
cal = [(mpf(0), mpf(0)), (mpf(2), mpf(0)), (mpf(1), mpf("0.05"))]
psi_c, br_c = mec(cal)
say("  mec  = %s  (branch %s)" % (mp.nstr(psi_c, 20), br_c))
al, be, ga = bary_weights(cal)
say("  circumradius branch would need barycentric weights (%s, %s, %s) -- one NEGATIVE (obtuse)"
    % (mp.nstr(al, 8), mp.nstr(be, 8), mp.nstr(ga, 8)))
say("  => MEC != circumradius when obtuse; the diameter branch is the correct one here.")


r0a = roots(HA, CA, R)
r0b = roots(HA, CB, R)
# choose the near root for each site: the one whose disk contains b (=HB) on its boundary
def near(a_roots):
    m1 = abs(nrm(sub(HB, a_roots[0])) - R)
    m2 = abs(nrm(sub(HB, a_roots[1])) - R)
    return a_roots[0] if m1 < m2 else a_roots[1]


q0 = near(r0a)
q4 = near(r0b)
say("a = hub A (cert 2) = (%.12f, %.12f) ; b = hub B (cert 0) = (%.12f, %.12f)" % (HA[0], HA[1], HB[0], HB[1]))
say("central near roots q_0 = (%.12f, %.12f) |q_0-b|-r = %+.2e ; q_4 = (%.12f, %.12f) |q_4-b|-r = %+.2e"
    % (q0[0], q0[1], float(nrm(sub(HB, q0)) - R), q4[0], q4[1], float(nrm(sub(HB, q4)) - R)))
pins = {p: pin(*p, r=R) for p in FANB}
for p, q in pins.items():
    say("  fan-B pin %s at (%.9f, %.9f) ; |pin-b|-r = %+.2e" % (p, q[0], q[1], float(nrm(sub(HB, q)) - R)))
say("")
CENTRES = [("central0", q0), ("central4", q4)] + [("pin%s" % (p,), pins[p]) for p in FANB]
say("triples (psi, branch, singleton at b, max gap):")
rows = []
for (n1, c1), (n2, c2), (n3, c3) in itertools.combinations(CENTRES, 3):
    psi, br = mec([c1, c2, c3])
    single, gaps = inward_and_gaps(HB, [c1, c2, c3], R)
    bw = bary_weights([c1, c2, c3])
    rows.append((float(psi - R), (n1, n2, n3), float(psi), br, single, max(gaps),
                 all(w > 0 for w in bw), [float(w) for w in bw]))
rows.sort()
say("  all triples sorted by psi - r (largest first shown last); singleton = (max gap <= 180 deg):")
for (d, names, psi, br, single, mg, posw, bw) in rows[-8:]:
    say("  psi - r = %+.3e  psi=%.15f  %s  %s  singleton=%s (max gap %.2f deg)  pos-bary=%s"
        % (d, psi, names, br, single, mg, posw))
say("")
tight = [r for r in rows if abs(r[0]) < 1e-12]
say("tight triples (|psi-r| < 1e-12): %d" % len(tight))
for (d, names, psi, br, single, mg, posw, bw) in tight:
    say("   %s : psi-r = %+.3e | branch %s | max gap %.2f deg -> singleton=%s | bary weights %s (all>0: %s)"
        % (names, d, br, mg, single, [round(w, 6) for w in bw], posw))
say("")
say("emptiness-witness search (psi > r strictly): %s"
    % ("none among these triples at this candidate (all psi <= r)" if max(r[0] for r in rows) <= 0
       else "FOUND: " + str([(r[1], r[0]) for r in rows if r[0] > 0])))
acute = [r for r in rows if r[3] == "circumcircle" and r[6]]
say("acute positive-barycentric triples: %d (largest psi - r = %s)"
    % (len(acute), ("%+.3e" % max(r[0] for r in acute)) if acute else "n/a"))
if acute:
    (d, names, psi, br, single, mg, posw, bw) = max(acute, key=lambda r: r[0])
    say("   example: %s  psi-r=%+.3e  bary=(%s)  max gap %.2f deg  singleton=%s"
        % (names, d, [round(w, 6) for w in bw], mg, single))
json.dump(dict(q0=[str(z) for z in q0], q4=[str(z) for z in q4],
               triples=[dict(names=list(n), psi_minus_r=d, branch=br, singleton=single)
                        for d, n, psi, br, single, mg in rows[:12]]),
          io.open(HERE / "central_tight_triple.json", "w"), indent=1)
(HERE / "central_tight_triple.out.txt").write_text("\n".join(OUT) + "\n", encoding="utf-8")
say("")
say("wrote central_tight_triple.json / .out.txt")
