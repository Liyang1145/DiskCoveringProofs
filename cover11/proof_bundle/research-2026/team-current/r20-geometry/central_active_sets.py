"""r20-geometry Round-7: joint central-coupling active sets on the certified q0(6,7) object.

Uses ONLY: (a) the crescent/angular normal form owned by r20-alternative (C894: rho(a,b,c) <= r
<=> angle acb in [alpha, pi-alpha], alpha = asin(d/2r), d = |a-b|; NOT re-derived here),
(b) the certified hubs (certified_object.json labels 0 and 2 = lead hubs 10 and 9),
(c) the two central ring sites (certified-object labels 5 and 6 = lead labels 0 and 4).
Output: which of the finite strata of Theorem D (CENTRAL-COUPLING-NORMAL-FORMS.md) are active.
No grid, no claim.  Repro: py -3 -B -X utf8 research-2026/team-current/r20-geometry/central_active_sets.py
"""
import io, json
from mpmath import mp, mpf, sqrt, asin, acos, cos, sin, atan2, pi as MP_PI
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
HA, HB = C[2], C[0]                      # certified-object hubs (lead 9 and 10)
CA, CB = C[5], C[6]                      # central ring sites (lead 0 and 4)
RING = [1, 3, 4, 5, 6, 7, 8, 9, 10]
FAN4 = [(5, 7), (7, 1), (1, 8), (8, 6)]                    # hub A (cert 2)
FAN5 = [(6, 4), (4, 9), (9, 10), (10, 3), (3, 5)]          # hub B (cert 0)


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def mul(s, a):
    return (s * a[0], s * a[1])


def nrm(a):
    return sqrt(a[0] ** 2 + a[1] ** 2)


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1]


def angle(P, Q, S):
    """angle PQS in [0,pi]"""
    u, v = sub(P, Q), sub(S, Q)
    return acos(max(mpf(-1), min(mpf(1), dot(u, v) / (nrm(u) * nrm(v)))))


def pin(i, j, r):
    ci, cj = C[i], C[j]
    m = mul(mpf(1) / 2, add(ci, cj))
    dv = sub(cj, ci)
    d = nrm(dv)
    n = (-dv[1] / d, dv[0] / d)
    k = sqrt(r * r - d * d / 4)
    p1, p2 = sub(m, mul(k, n)), add(m, mul(k, n))
    return (p1, p2) if nrm(p1) < nrm(p2) else (p2, p1)


PINS_A = [pin(i, j, R)[0] for (i, j) in FAN4]
PINS_B = [pin(i, j, R)[0] for (i, j) in FAN5]

d = nrm(sub(HA, HB))
alpha = asin(d / (2 * R))
say("certified q0(6,7): hubs (lead 9)=%.12f,%.12f  (lead 10)=%.12f,%.12f" % (HA[0], HA[1], HB[0], HB[1]))
say("r = %s ; rho = 1-r = %s" % (mp.nstr(R, 15), mp.nstr(RHO, 15)))
say("chord d = |hA-hB| = %s ; 2r = %s ; d <= 2r ? %s" % (mp.nstr(d, 15), mp.nstr(2 * R, 12), d <= 2 * R))
say("alpha_d = asin(d/2r) = %s rad (%.4f deg)" % (mp.nstr(alpha, 15), float(alpha * 180 / MP_PI)))
for tag, c in (("c_a (lead 0, cert 5)", CA), ("c_b (lead 4, cert 6)", CB)):
    th = angle(HA, c, HB)
    say("  site %s: angle(hA,c,hB) = %s rad (%.4f deg) ; in [alpha,pi-alpha] ? %s ; Rc^2-r^2 sign: %s"
        % (tag, mp.nstr(th, 15), float(th * 180 / MP_PI),
           alpha <= th <= MP_PI - alpha, "<=0" if alpha <= th <= MP_PI - alpha else ">0"))
    say("      |c-p_+|/|c-p_-| (crescent side/strictness): side = %s"
        % ("+n" if dot(sub(c, mul(mpf(1) / 2, add(HA, HB))), (-(HB[1] - HA[1]), (HB[0] - HA[0]))) > 0 else "-n"))
say("")
say("fan-side active sets (Theorem A candidates):")
sa = min(nrm(sub(HA, p)) - R for p in PINS_A)
sb = min(nrm(sub(HB, p)) - R for p in PINS_B)
say("  hub A: max_j |hA - p_j| - r = %+.3e (<=0 => inside all fan disks; =0 => active)" % float(sa))
say("  hub B: max_j |hB - p_j| - r = %+.3e" % float(sb))
say("  |hA| = %s < rho ? %s ; |hB| = %s < rho ? %s (strict hubs)"
    % (mp.nstr(nrm(HA), 12), nrm(HA) < RHO, mp.nstr(nrm(HB), 12), nrm(HB) < RHO))
say("")
say("Theorem D stratification (active sets) on the object:")
say("  central equalities: R_{c_a}=r ? %s ; R_{c_b}=r ? %s  (angle-level: the interval is tight iff th in {alpha,pi-alpha})"
    % (abs(angle(HA, CA, HB) - alpha) < mpf("1e-10"), abs(angle(HA, CB, HB) - alpha) < mpf("1e-10")))
say("  chord stratum d=2r: %s (d/2r = %s)" % (d == 2 * R, mp.nstr(d / (2 * R), 12)))
say("  fan-disk active: hub A %s (slack %+.2e) ; hub B %s (slack %+.2e)"
    % ("YES" if abs(sa) < mpf("1e-12") else "no", float(sa),
       "YES" if abs(sb) < mpf("1e-12") else "no", float(sb)))

json.dump(dict(r=str(R), rho=str(RHO), d=str(d), alpha=str(alpha),
               angle_ca=str(angle(HA, CA, HB)), angle_cb=str(angle(HA, CB, HB)),
               fanA_slack=str(sa), fanB_slack=str(sb),
               hubA_norm=str(nrm(HA)), hubB_norm=str(nrm(HB))),
          io.open(HERE / "central_active_sets.json", "w"), indent=1)
(HERE / "central_active_sets.out.txt").write_text("\n".join(OUT) + "\n", encoding="utf-8")
say("")
say("wrote central_active_sets.json / .out.txt")
