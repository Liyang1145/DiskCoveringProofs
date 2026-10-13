"""Experiment 1: flat-slice maximum vs general (non-flat) maximum of the seven-factor
objective, current frozen dual (lead/joint_nested_frozen.json, SHA 5671967c...).

Question (new proposition tested):
   P-FLAT-DOM:  sup_{general patch} F  =  sup_{alpha2 = pi flat slice} F
i.e. does the flat slice (the part covered by the C870-C876 certificates) dominate the
whole remaining non-flat domain of the same relaxation?

Budget: <= 20 bounded optimization starts in total for this file.
Outputs: exp1_results.json (all x vectors, values, margin minima, legality flags).
"""
import json, math, sys, time
from pathlib import Path
import numpy as np
from scipy.optimize import differential_evolution, minimize, NonlinearConstraint

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import r20_lib as L

PI, TAU, R = L.PI, L.TAU, L.R
STARTS = {"flat": 0, "gen": 0}
BUDGET = 20
RES = []

# ------------------------------------------------------------------ flat chart ------
FB = [(TAU, 1), (.0233, PI), (.19, 1), (.0233, PI), (.19, 1), (1e-5, 1 - 1e-5), (0, 1)]


def flat_ok(x):
    d = L.flat_args(x)
    if d is None:
        return None
    t = x[0]
    mg = []
    for (a, u, v) in [d["sectors"][0], d["sectors"][2]]:
        m = L.sector_margin(a, u, v, t)
        if m is None:
            return None
        mg += m
    mg += [d["b1"], d["b2"], PI / 2 - d["b1"], PI / 2 - d["b2"],
           2 * t * math.cos(d["b1"]) - R * (t * t + t * t),
           2 * t * math.cos(d["b2"]) - R * (t * t + t * t)]
    return mg


def neg_flat(x):
    d = L.flat_args(x)
    if d is None:
        return 1e3
    m = flat_ok(x)
    if m is None or min(m) < -1e-9:
        return 1e3 - min(m) if m else 1e3
    return -L.flat_value(d)


MFLAT, MGEN = 14, 35


def pad(m, M):
    if m is None:
        return np.full(M, -1.0)
    m = np.asarray(m, dtype=float).ravel()
    if len(m) == M:
        return m
    if len(m) < M:
        return np.r_[m, np.full(M - len(m), -1.0)]
    return m[:M]


def cons_flat(x):
    return pad(flat_ok(x), MFLAT)


def run_flat(seed, x0=None):
    STARTS["flat"] += 1
    n = STARTS["flat"] + STARTS["gen"]
    assert n <= BUDGET, "budget exceeded"
    cons = NonlinearConstraint(cons_flat, 0, np.inf)
    if x0 is None:
        de = differential_evolution(neg_flat, FB, constraints=cons, seed=seed,
                                    popsize=12, maxiter=140, polish=False)
        x0 = de.x
    loc = minimize(neg_flat, x0, method="SLSQP", bounds=FB,
                   constraints={"type": "ineq", "fun": cons_flat},
                   options={"maxiter": 400, "ftol": 1e-12})
    best = loc if -loc.fun <= -neg_flat(x0) else type("o", (), dict(x=x0, fun=neg_flat(x0)))
    d = L.flat_args(best.x)
    rec = dict(kind="flat", seed=seed, value=float(-best.fun), x=list(map(float, best.x)),
               minmargin=float(min(cons_flat(best.x))), legal=bool(d is not None),
               b1=d["b1"], b2=d["b2"], A=d["A"], H=d["H"], t=float(best.x[0]))
    RES.append(rec)
    print("  flat start seed=%d  value=%.10f  minmargin=%.2e" % (seed, rec["value"], rec["minmargin"]), flush=True)
    return rec


# ----------------------------------------------------------------- general chart ----
GB = [(TAU, 1), (.0233, PI), (1e-4, 1), (1e-4, 1), (.0233, PI), (1e-4, 1),
      (.0233, PI), (1e-4, 1), (1e-4, 1 - 1e-4), (0.02, 2 * R)]


def build_p(x):
    """x = (t,a1,u1,s1,a2,s2,a3,v3, Afrac, H) -> parameter dict with A = Afrac*(b1+b2)."""
    p0 = dict(t=x[0], a1=x[1], u1=x[2], s1=x[3], a2=x[4], s2=x[5], a3=x[6], v3=x[7],
              A=0.0, H=x[9])
    bb = L.closure_b(p0)
    if bb is None:
        return None
    b1, b2 = bb
    if not (0 < b1 < PI / 2 and 0 < b2 < PI / 2):
        return None
    p0["A"] = x[8] * (b1 + b2)
    return p0


def gen_ok_np(x):
    p = build_p(x)
    if p is None:
        return np.full(MGEN, -1.0), None
    names, mg = L.gen_margins(p)
    return pad(mg, MGEN), p


def neg_gen(x):
    mg, p = gen_ok_np(x)
    if min(mg) < -1e-9:
        return 1e3 - min(mg)
    d = L.gen_args(p)
    if d is None:
        return 1e3
    return -L.gen_value(d)


def cons_gen(x):
    mg, p = gen_ok_np(x)
    return pad(mg, MGEN)


def run_gen(seed, x0=None, tag=""):
    STARTS["gen"] += 1
    n = STARTS["flat"] + STARTS["gen"]
    assert n <= BUDGET, "budget exceeded"
    if x0 is None:
        de = differential_evolution(neg_gen, GB, constraints=NonlinearConstraint(cons_gen, 0, np.inf),
                                    seed=seed, popsize=10, maxiter=110, polish=False)
        x0 = de.x
    loc = minimize(neg_gen, x0, method="SLSQP", bounds=GB,
                   constraints={"type": "ineq", "fun": cons_gen},
                   options={"maxiter": 400, "ftol": 1e-12})
    ok = -loc.fun <= -neg_gen(x0)
    xb = loc.x if ok else np.array(x0)
    mg, p = gen_ok_np(xb)
    d = L.gen_args(p)
    rec = dict(kind="gen", tag=tag, seed=seed, value=float(-neg_gen(xb)), x=list(map(float, xb)),
               minmargin=float(min(mg)), legal=bool(d is not None and min(mg) >= -1e-8))
    if d is not None:
        rec.update(t=p["t"], a2=p["a2"], s1=p["s1"], s2=p["s2"], b1=d["b1"], b2=d["b2"],
                   A=d["A"], B=d["B"], H=d["H"], hubnorm=d["hubnorm"], w2=d["w2"],
                   flatness=float(PI - p["a2"]))
    RES.append(rec)
    print("  gen  start seed=%d %s value=%.10f  minmargin=%.2e a2=%.6f t=%.6f" %
          (seed, tag, rec["value"], rec["minmargin"], rec.get("a2", float("nan")), rec.get("t", float("nan"))), flush=True)
    return rec


if __name__ == "__main__":
    t0 = time.time()
    print("== flat-slice maximum (3 starts) ==")
    f1 = run_flat(11)
    f2 = run_flat(12)
    # third flat start: embed the recorded round-18 cluster optimum region
    f3 = run_flat(13, x0=np.array([1.0, 2.6874, 1.0, 2.6808, 1.0, 0.4996, 1.0]))
    flat_best = max(RES, key=lambda r: r["value"])
    print("flat best =", flat_best["value"], " x=", [round(v, 6) for v in flat_best["x"]])

    print("== general (non-flat) chart maximum (13 starts) ==")
    # (i) embed the flat optimum (alpha2 = pi, s1 = s2 = t) then interior starts
    xf = list(flat_best["x"])
    x_embed = [xf[0], xf[1], xf[2], xf[0], PI, xf[0], xf[3], xf[4], xf[5], flat_best["H"]]
    run_gen(101, x0=np.array(x_embed), tag="flat-embed")
    # interior perturbations of the flat optimum (alpha2 < pi, s1,s2 < t)
    for k, (dA, ds, dt) in enumerate([(0.02, 0.01, 0.0), (0.10, 0.03, 0.0), (0.30, 0.05, 0.0),
                                      (0.02, 0.01, -0.01), (0.50, 0.10, -0.02)]):
        xp = np.array(x_embed, dtype=float)
        xp[4] = PI - dA                      # alpha2
        xp[3] = max(0.05, xp[0] - ds)        # s1
        xp[5] = max(0.05, xp[0] - ds)        # s2
        xp[0] = min(1.0, max(TAU, xp[0] + dt))
        run_gen(200 + k, x0=xp, tag="perturb%.2f/%.2f" % (dA, ds))
    for seed in (301, 302, 303, 304, 305):
        run_gen(seed, tag="DE")
    gb = max([r for r in RES if r["kind"] == "gen"], key=lambda r: r["value"])
    print("gen  best =", gb["value"], " a2=%.8f flatness=%.3e t=%.6f s1=%.4f s2=%.4f" %
          (gb.get("a2", -1), gb.get("flatness", -1), gb.get("t", -1), gb.get("s1", -1), gb.get("s2", -1)))
    out = dict(budget=BUDGET, starts=STARTS, flat_best=flat_best, gen_best=gb, results=RES,
               frozen_dual_sha="5671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb",
               elapsed=time.time() - t0)
    (HERE / "exp1_results.json").write_text(json.dumps(out, indent=1))
    print("wrote exp1_results.json  elapsed %.1f s" % (time.time() - t0))
