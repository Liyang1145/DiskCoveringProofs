"""Final bounded checks (A LP-dual algebra, B clip-routine audit, C necessity/provenance).
Writes a log; intended to be run in the background.  B is a small-dimension brute-force
comparison so it cannot blow up: 8 base rows + simplex in R^10 => C(17,9) = 24310 solves.
"""
import itertools
import json
import hashlib
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAD = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead")
sys.path.insert(0, str(LEAD))
from q10_rational_polytope_audit import clip, scalar      # noqa: E402

LOG = open(HERE / "final-chain-check.log", "w", encoding="utf-8")


def log(*a):
    print(*a, flush=True)
    print(*a, file=LOG, flush=True)


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def A():
    d = json.loads((LEAD / "q10-halfspace-angle-dual.json").read_text(encoding="utf-8"))
    obj = json.loads((LEAD / "q10-c1366-domain.json").read_text(encoding="utf-8"))["polytope"]
    N = [list(map(Q, row[0])) for row in obj["inequalities"]]
    used = set()
    nb = 0
    positive = 0
    maxabs = Q(0)
    for r in d["rows"]:
        for cert in r["dual"]:
            nb += 1
            y = {int(k): Q(v) for k, v in cert["multipliers"]}
            positive += sum(1 for v in y.values() if v > 0)
            used |= set(y.keys())
        maxabs = max(maxabs, abs(Q(r["delta_lower"])), abs(Q(r["delta_upper"])))
    out = dict(n_certificates=nb, n_positive_multipliers=positive,
               rows_used=sorted(used), n_rows_used=len(used), n_rows_total=len(N),
               maxabs_delta=str(maxabs), maxabs_float=float(maxabs),
               one_over_200=0.005, inside_box=float(maxabs) < 0.005,
               domain_hash_ok=(d["domain_sha256"] == sha(LEAD / "q10-c1366-domain.json")))
    return out


def enumerate_vertices(N, rhs):
    verts = set()
    rows = list(zip(N, rhs))
    m = len(rows)
    for comb in itertools.combinations(range(m), 9):
        A_ = [[Q(1)] * 10 + [Q(1)]] + [[x for x in rows[i][0]] + [rows[i][1]] for i in comb]
        r = 0
        ok = True
        for col in range(10):
            p = None
            for i in range(r, 10):
                if A_[i][col] != 0:
                    p = i
                    break
            if p is None:
                ok = False
                break
            A_[r], A_[p] = A_[p], A_[r]
            pr = A_[r]
            for i in range(10):
                if i != r and A_[i][col] != 0:
                    f = A_[i][col] / pr[col]
                    A_[i] = [a - f * c for a, c in zip(A_[i], pr)]
            r += 1
        if not ok:
            continue
        x = tuple(A_[i][10] / A_[i][i] for i in range(10))
        if all(sum(a * y for a, y in zip(row, x)) >= rr for row, rr in rows):
            verts.add(x)
    return verts


def B(seed, n_extra):
    import random
    random.seed(seed)
    base = [([Q(1 if i == j else 0) for i in range(10)], Q(0)) for j in range(10)]
    for _ in range(n_extra):
        n = [Q(random.randint(-3, 3)) for _ in range(10)]
        if all(v == 0 for v in n):
            continue
        base.append((n, Q(random.randint(-2, 2))))
    N = [b[0] for b in base]
    rhs = [b[1] for b in base]
    V = enumerate_vertices(N, rhs)
    if not V:
        return dict(seed=seed, n_extra=n_extra, status="empty")
    cs = list(zip(N, rhs))
    newn = tuple(Q(random.randint(-3, 3)) for _ in range(10))
    newr = Q(random.randint(-2, 2))
    on, off = clip(sorted(V), cs, newn, newr)
    N2 = N + [list(newn)]
    rhs2 = rhs + [newr]
    V2 = enumerate_vertices(N2, rhs2)
    bf_on = {x for x in V2 if sum(a * b for a, b in zip(newn, x)) >= newr}
    bf_off = {x for x in V2 if sum(a * b for a, b in zip(newn, x)) <= newr}
    return dict(seed=seed, n_extra=n_extra, base_rows=len(N), base_vertices=len(V),
                on_set_equal=(set(on) == bf_on), off_set_equal=(set(off) == bf_off),
                n_on=len(set(on)), n_bf_on=len(bf_on),
                n_off=len(set(off)), n_bf_off=len(bf_off))


def C():
    out = {}
    dom = json.loads((LEAD / "q10-c1366-domain.json").read_text(encoding="utf-8"))
    a = json.loads((LEAD / "q10-metric-round8-audit.json").read_text(encoding="utf-8"))
    out["round8_status"] = a["status"]
    base = a["domain_sha256"]
    out["audit_base_equals_c1366_source"] = (base == dom["source_sha256"])
    # locate the base file by hash, but bound the scan (c1365 is the known producer input)
    cand = LEAD / "q10-c1365-domain.json"
    out["c1365_is_base"] = (cand.exists() and sha(cand) == base)
    cases = a["results"]
    out["n_cases"] = len(cases)
    out["n_cases_closed"] = sum(1 for c in cases if not c["open_cells"])
    out["open_cases"] = [c["case"] for c in cases if c["open_cells"]]
    out["excluded_leaves_per_case"] = [len(c["excluded_leaves"]) for c in cases]
    # per-case stored files for round8
    files = sorted(LEAD.glob("q10-metric-round8-*.json"))
    out["n_case_files"] = len(files)
    good = 0
    bad = []
    for f in files:
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except Exception:
            bad.append(f.name)
            continue
        if d.get("source_sha256") == base:
            good += 1
        else:
            bad.append(f.name)
    out["case_files_source_matches_base"] = good
    out["case_files_bad"] = bad[:5]
    acuts = [(tuple(sorted(c["indices"])), c["sense"], str(c["fraction_of_total"]))
             for c in a["cuts"]]
    dcuts = [(tuple(sorted(c["cut"]["indices"])), c["cut"]["sense"],
              str(c["cut"]["fraction_of_total"])) for c in dom["cuts"]]
    out["cuts_equal"] = (acuts == dcuts)
    out["audit_cuts"] = [[list(i), s, t] for i, s, t in acuts]
    t = json.loads((LEAD / "q10-fan-transport.json").read_text(encoding="utf-8"))
    out["transport_status"] = t["status"]
    out["transport_n_runs"] = len(t["runs"])
    out["transport_source_is_c1365"] = (t["source_sha256"] == sha(cand)) if cand.exists() else None
    run = t["runs"][0]
    out["transport_run_keys"] = sorted(run.keys())
    sp = run.get("site_permutation")
    if isinstance(sp, dict):
        vals = sorted(int(v) for v in sp.values())
    else:
        vals = sorted(int(v) for v in sp)
    out["transport_site_perm_bijection"] = (vals == list(range(14)))
    dp = run.get("deficit_permutation")
    dvals = sorted(int(v) for v in (dp.values() if isinstance(dp, dict) else dp))
    out["transport_deficit_perm_bijection"] = (dvals == list(range(10)))
    return out


if __name__ == "__main__":
    res = {}
    log("A LP-dual algebra...")
    res["A"] = A()
    log(json.dumps(res["A"], indent=1)[:1200])
    log("B clip audit (small brute force)...")
    res["B"] = [B(s, e) for s in (1, 2) for e in (6, 8)]
    log(json.dumps(res["B"], indent=1)[:1500])
    log("C necessity/provenance chain...")
    res["C"] = C()
    log(json.dumps(res["C"], indent=1)[:2000])
    (HERE / "final-chain-check.json").write_text(json.dumps(res, indent=1, default=str),
                                                 encoding="utf-8")
    log("DONE")
