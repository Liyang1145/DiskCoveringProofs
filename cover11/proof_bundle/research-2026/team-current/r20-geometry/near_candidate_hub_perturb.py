"""r20-geometry Round-12 (lead 9b06ab5b): bounded near-candidate fixed-rings test-level experiment.

Goal (bounded, <= 20 hub perturbations): with the certified 9 ring centres FIXED and their 9 chain pins
(4 + 5) assigned to the two hubs as in the certified fan structure, find a hub perturbation such that
  (a) every pin is still covered by its assigned hub (the ASSIGNMENT stays feasible), and
  (b) some INTERIOR point of a residual arc is covered by NEITHER hub.
If found: dump all pins + the residual arc data and certify the strict margin.  If not found: report
"not found" and switch to the endpoint-sufficiency condition (per lead).
Claim scope on success: only "vertex (pin) coverage is NOT sufficient" -- NOT "the line cannot be
eliminated".  No 12-D numerics; this is a fixed-rings small search + exact verification of the witness.

Repro: py -3 -B -X utf8 research-2026/team-current/r20-geometry/near_candidate_hub_perturb.py
"""
import io, json
from mpmath import mp, mpf, sqrt, cos, sin, atan2, acos, pi as MP_PI
from pathlib import Path
mp.dps = 40
HERE = Path(__file__).resolve().parent
ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s)


OBJ = json.load(io.open(ROOT / "n11/upper/certified_object.json", encoding="utf-8"))
SC = mpf(10) ** int(OBJ["decimals"])
CENT = [(mpf(int(a)) / SC, mpf(int(b)) / SC) for a, b in OBJ["centers_scaled_1e17"]]
R_CERT = mpf(OBJ["certified_interval"]["lo"])

RINGS = [7, 1, 8, 6, 4, 9, 10, 3, 5]            # cert cyclic order of the nine rings
HUBA, HUBB = 2, 0                                # cert labels: hub A = 2, hub B = 0
FAN_A_PAIRS = [(5, 7), (7, 1), (1, 8), (8, 6)]
FAN_B_PAIRS = [(6, 4), (4, 9), (9, 10), (10, 3), (3, 5)]


def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def add(p, q):
    return (p[0] + q[0], p[1] + q[1])


def mul(s, p):
    return (s * p[0], s * p[1])


def nrm(p):
    return sqrt(p[0] ** 2 + p[1] ** 2)


def roots(a, c, r):
    m = mul(mpf(1) / 2, add(a, c))
    dv = sub(c, a)
    d = nrm(dv)
    if d == 0 or d > 2 * r:
        return None
    nn = (-dv[1] / d, dv[0] / d)
    k = sqrt(r * r - d * d / 4)
    return (sub(m, mul(k, nn)), add(m, mul(k, nn)))


def near_pin(i, j, r):
    pr = roots(CENT[i], CENT[j], r)
    if pr is None:
        return None
    o = (mpf(0), mpf(0))
    return pr[0] if nrm(sub(pr[0], o)) < nrm(sub(pr[1], o)) else pr[1]


def run(r, verbose=True):
    """one experiment at radius r; returns dict or None."""
    pins_A = [near_pin(i, j, r) for (i, j) in FAN_A_PAIRS]
    pins_B = [near_pin(i, j, r) for (i, j) in FAN_B_PAIRS]
    hA = (CENT[HUBA][0], CENT[HUBA][1])
    hB = (CENT[HUBB][0], CENT[HUBB][1])
    rho = 1 - r
    if verbose:
        say("r = %s (%.9f) ; hub A = (%.9f, %.9f) |hA| = %.9f < rho = %.9f ; hub B |hB| = %.9f"
            % (mp.nstr(r, 12), float(r), float(hA[0]), float(hA[1]), float(nrm(hA)), float(rho), float(nrm(hB))))
        say("pin margins at the candidate (r - |h - pin|):")
        for nm, hs, ps in (("A", hA, pins_A), ("B", hB, pins_B)):
            say("  fan %s: %s" % (nm, ", ".join("%+.6f" % float(r - nrm(sub(h, p))) for h, p in zip([hs] * len(ps), ps))))
    okA = all(nrm(sub(hA, p)) <= r + 1e-30 for p in pins_A)
    okB = all(nrm(sub(hB, p)) <= r + 1e-30 for p in pins_B)
    if not (okA and okB):
        say("  candidate assignment not feasible at this r -> skip")
        return None
    # residual arcs: for each ring i, directions u on circle(c_i,r) with |c_i+ru| <= 1 and |c_i+ru-c_j| > r
    nstep = 4000
    arcs = {}
    for idx in RINGS:
        ci = CENT[idx]
        good = []
        for k in range(nstep):
            th = 2 * MP_PI * k / nstep
            u = (cos(th), sin(th))
            x = add(ci, mul(r, u))
            if nrm(x) > 1:
                continue
            if all(nrm(sub(x, CENT[j])) > r for j in RINGS if j != idx):
                good.append(th)
        # group into contiguous intervals
        iv, cur = [], None
        for k, th in enumerate(good):
            if cur is None:
                cur = [th, th]
            elif abs(th - cur[1]) < 2 * MP_PI / nstep * 1.5:
                cur[1] = th
            else:
                iv.append(tuple(cur))
                cur = [th, th]
        if cur:
            iv.append(tuple(cur))
        if iv:
            arcs[idx] = iv
    tot = sum(len(v) for v in arcs.values())
    if verbose:
        say("residual arcs found on rings %s (total %d intervals)" % (sorted(arcs), tot))
    # candidate interior points: midpoints of the arcs (skip near endpoints)
    cands = []
    for idx, ivs in arcs.items():
        for (a0, a1) in ivs:
            th = (a0 + a1) / 2
            x = add(CENT[idx], mul(r, (cos(th), sin(th))))
            cands.append((idx, th, x, a1 - a0))
    cands.sort(key=lambda t: -t[3])
    if verbose:
        say("largest residual arc: ring %d, angular width %.4f deg, interior point (%.9f, %.9f)"
            % (cands[0][0], float(cands[0][3] * 180 / MP_PI), float(cands[0][2][0]), float(cands[0][2][1])))
    # bounded perturbation search: move hub B away from a chosen interior point (<=20 trials)
    trials = 0
    found = None
    for (idx, th, x, w) in cands[:4]:
        d = sub(hB, x)
        nd = nrm(d)
        if nd == 0:
            continue
        v = (d[0] / nd, d[1] / nd)
        for t in [mpf("0.01") * k for k in range(1, 6)]:
            trials += 1
            if trials > 20:
                break
            hB2 = add(hB, mul(t, v))
            if nrm(hB2) >= rho:
                continue
            pins_ok = all(nrm(sub(hB2, p)) <= r for p in pins_B)
            miss = nrm(sub(x, hB2)) > r and nrm(sub(x, hA)) > r
            if pins_ok and miss:
                found = dict(ring=idx, theta=th, x=x, width=w, t=t, hB2=hB2,
                             pin_margin=min(r - nrm(sub(hB2, p)) for p in pins_B),
                             miss_margin=min(nrm(sub(x, hB2)) - r, nrm(sub(x, hA)) - r))
                break
        if found:
            break
    if verbose:
        say("perturbation trials used: %d (cap 20)" % trials)
    return dict(r=r, pins_A=pins_A, pins_B=pins_B, hA=hA, hB=hB, found=found, arcs=arcs)


for rr in (R_CERT, mpf("0.38")):
    say("=" * 100)
    say("EXPERIMENT at r = %s" % mp.nstr(rr, 16))
    say("=" * 100)
    res = run(rr)
    if res and res["found"]:
        f = res["found"]
        say("FOUND (r = %s): perturb hub B by t = %s away from residual-arc interior point" % (mp.nstr(rr, 12), mp.nstr(f["t"], 8)))
        say("  ring %d arc (width %.4f deg) interior point x = (%.9f, %.9f)" % (f["ring"], float(f["width"] * 180 / MP_PI), float(f["x"][0]), float(f["x"][1])))
        say("  new hub B' = (%.9f, %.9f) ; all five fan-B pins covered, min pin margin = %+.3e" % (float(f["hB2"][0]), float(f["hB2"][1]), float(f["pin_margin"])))
        say("  x covered by hub B'? distance - r = %+.3e ; by hub A? %+.3e -> strict miss margin %+.3e"
            % (float(nrm(sub(f["x"], f["hB2"])) - rr), float(nrm(sub(f["x"], res["hA"])) - rr), float(f["miss_margin"])))
        say("  => VERTEX (pin) COVERAGE IS NOT SUFFICIENT: the 9-pin assignment is feasible yet an interior")
        say("     point of a residual arc is covered by neither hub. (No claim about the 2-D line parameter.)")
        dump = dict(
            r=str(rr), hubA=[mp.nstr(z, 25) for z in res["hA"]], hubB=[mp.nstr(z, 25) for z in res["hB"]],
            hubB_perturbed=[mp.nstr(z, 25) for z in f["hB2"]],
            pins_A=[[mp.nstr(z, 25) for z in p] for p in res["pins_A"]],
            pins_B=[[mp.nstr(z, 25) for z in p] for p in res["pins_B"]],
            missed_point=[mp.nstr(z, 25) for z in f["x"]], missed_ring=f["ring"], arc_width_deg=float(f["width"] * 180 / MP_PI),
            pin_margin=str(f["pin_margin"]), miss_margin=str(f["miss_margin"]),
            perturbation_t=str(f["t"]))
        io.open(HERE / "near_candidate_hub_perturb.json", "w").write(json.dumps(dump, indent=1))
        say("  dumped: near_candidate_hub_perturb.json")
        break
    else:
        say("NOT FOUND at r = %s within the bounded search." % mp.nstr(rr, 12))

io.open(HERE / "near_candidate_hub_perturb.out.txt", "w", encoding="utf-8").write("\n".join(OUT) + "\n")
print()
print("wrote near_candidate_hub_perturb.out.txt")
