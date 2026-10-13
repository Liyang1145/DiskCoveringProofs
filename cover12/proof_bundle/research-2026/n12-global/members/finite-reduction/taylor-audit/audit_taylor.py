#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Independent audit kernel for the lead's network Taylor certificates (v2).

Object under audit (read-only): evidence/network-certified-*.json
claim per certificate: for the recorded exact rational stresses alpha, the exact
rational simplex reference y, and the recorded kappa, the full 9-gap-simplex
Taylor bound

    E0 + min_vertex(linear) - kappa * max_vertex(norm^2) / 2   >   U^2

holds, where q comes from Dirichlet elimination of the internal nodes, M is the
Schur/Hessian lower matrix with cos(dL) = T_d(1-2U^2), and M + kappa I is positive
definite on the full 9x9 space.

INDEPENDENCE (different inference / implementation from the lead's code):
  1. Schur/Dirichlet elimination computed twice in EXACT fractions.Fraction:
     (a) in-place symmetric elimination (lead's node order);
     (b) a different path: solve A_int X = B by Gauss-Jordan, S = L_aa - B^T X.
     Both must agree; positivity of pivots is then an exact rational statement,
     with no 10^-45 interval grid.
  2. M + kappa I positive definiteness by exact rational LDL (all pivots > 0).
  3. Trigonometry: BINARY fixed-point interval kernel (scale 2^-240, integer
     floor/ceil rounding), sin/cos by argument halving + double-angle identities
     from an alternating-series core with the explicit alternating remainder bound
     |R| <= first omitted term.  The lead uses a decimal 10^-45 interval grid and a
     40-term interval Taylor series with the Lagrange remainder.
  4. pi: independent Machin series with different truncation orders (exact rational
     alternating bounds), used to confirm that the recorded pi interval contains it.
  5. L = 2 asin U bracket re-verified as sin(L_lo/2) < U < sin(L_hi/2) with the
     independent fixed-point sin.

Scope / honest limits:
  * Only the certificate's own mathematical content is checked.  The geometric
    interface (radius<=U cover -> this witness network; anchor gap <= L) and the
    reading "energy > U^2 excludes the network" are NOT verified here.
  * A PASS is an audit reading, not a certification of the parent claim.
Usage: py -3 -B audit_taylor.py [name ...]        (default: the six T3 blocks)
       py -3 -B audit_taylor.py --files f1 f2 ... (explicit certificate paths)
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
N12 = HERE.parents[2]                       # .../n12-global
EV = N12 / "evidence"
OUT = HERE / "out"
OUT.mkdir(exist_ok=True)

U_DEC = F("0.361102963744508672616920293904")
U_REG = F(22568935234031792038557518369, 62500000000000000000000000000)
assert U_DEC == U_REG, "registered rational U and decimal U disagree"
U = U_REG
U2 = U * U


def fact(n):
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r


# ---------------------------------------------------------------- exact pi
def atan_iv(x: F, N: int):
    """Alternating bound for atan(x), 0 < x < 1: consecutive partial sums bracket
    the true value."""
    s = F(0)
    for k in range(N):
        s += F((-1) ** k) * x ** (2 * k + 1) / F(2 * k + 1)
    nxt = F((-1) ** N) * x ** (2 * N + 1) / F(2 * N + 1)
    return (min(s, s + nxt), max(s, s + nxt))


def pi_independent(n1=110, n2=32):
    a = atan_iv(F(1, 5), n1)
    b = atan_iv(F(1, 239), n2)
    lo = 16 * a[0] - 4 * b[1]
    hi = 16 * a[1] - 4 * b[0]
    assert lo <= hi
    return (lo, hi)


# ------------------------------------------------- binary fixed-point kernel
K = 240
ONE = 1 << K


def to_fp(x):
    """Exact rational -> outward fixed-point integer interval."""
    x = F(x)
    n = x.numerator * ONE
    return (n // x.denominator, -((-n) // x.denominator))


def fp_add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def fp_sub(a, b):
    return (a[0] - b[1], a[1] - b[0])


def fp_neg(a):
    return (-a[1], -a[0])


def fp_mul(a, b):
    p = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return (min(p) >> K, -((-max(p)) >> K))


def fp_scale(a, r):
    """Multiply interval a by the exact rational r, outward."""
    r = F(r)
    p, q = r.numerator, r.denominator
    lo, hi = a[0] * p, a[1] * p
    if p < 0:
        lo, hi = hi, lo
    return (lo // q, -((-hi) // q))


def fp_halve(a):
    return (a[0] // 2, -((-a[1]) // 2))


def fp_rem_bound(m, deg):
    """Integer >= 2^K * (m/2^K)^deg / deg!  (m, deg integers, m >= 0, deg >= 1)."""
    return -((-(m ** deg)) // (fact(deg) << (K * (deg - 1))))


def fp_sin_cos(X, N=26):
    """Rigorous sin/cos enclosure on a fixed-point interval X (|X| < 7)."""
    m = max(abs(X[0]), abs(X[1]))
    assert m < 7 * ONE
    if m <= ONE // 2:
        x2 = fp_mul(X, X)
        s = (0, 0)
        term = X
        for k in range(N):
            s = fp_add(s, term)
            term = fp_scale(fp_mul(term, x2), F(-1, (2 * k + 2) * (2 * k + 3)))
        rem = (0, 0)
        r = fp_rem_bound(m, 2 * N + 1)
        s = (s[0] - r, s[1] + r)
        c = (0, 0)
        term = (ONE, ONE)
        for k in range(N):
            c = fp_add(c, term)
            term = fp_scale(fp_mul(term, x2), F(-1, (2 * k + 1) * (2 * k + 2)))
        rc = fp_rem_bound(m, 2 * N)
        c = (c[0] - rc, c[1] + rc)
        return s, c
    s, c = fp_sin_cos(fp_halve(X), N)
    return fp_mul((2 * ONE, 2 * ONE), fp_mul(s, c)), \
        fp_sub((ONE, ONE), fp_mul((2 * ONE, 2 * ONE), fp_mul(s, s)))


def fp_sum(terms):
    a = (0, 0)
    for t in terms:
        a = fp_add(a, t)
    return a


# ---------------------------------------------------------------- graph
def build_graph(faces):
    """Independent reconstruction of the recorded edge list from the recorded faces,
    under the CLAIMED face mapping: nodes 0..nsites-1 are sites/hubs, nodes
    nf..nf+8 are the 9 ring anchors with edges anchor i - site i and anchor i -
    site (i+1)%9, and node nsites+i is the witness node of face i joined to its
    three vertices.  (nsites is read off the faces; the mapping is then CHECKED
    against the recorded edges, not assumed.)"""
    nsites = 1 + max(k for f in faces for k in f)
    nf = nsites + len(faces)
    edges = []
    for i in range(9):
        edges.append((nf + i, i))
        edges.append((nf + i, (i + 1) % 9))
    for i, f in enumerate(faces):
        assert len(f) == 3 and len(set(f)) == 3, f"face {i} not a 3-simplex: {f}"
        for k in f:
            edges.append((nsites + i, k))
    return nsites, nf, edges


def laplacian(edges, w, n):
    L = [[F(0)] * n for _ in range(n)]
    for (a, b), ww in zip(edges, w):
        L[a][a] += ww
        L[b][b] += ww
        L[a][b] -= ww
        L[b][a] -= ww
    return L


def schur_inplace(edges, w, nf):
    n = nf + 9
    A = laplacian(edges, w, n)
    piv = []
    for k in range(nf):
        p = A[k][k]
        if p <= 0:
            return None, piv, ("nonpositive Dirichlet pivot", k, str(p))
        piv.append(p)
        Ak = A[k]
        for i in range(k + 1, n):
            f = A[i][k] / p
            if f:
                Ai = A[i]
                for j in range(k + 1, n):
                    Ai[j] -= f * Ak[j]
    q = {(i, j): -A[nf + i][nf + j] for i in range(9) for j in range(i + 1, 9)}
    return q, piv, None


def schur_solve(edges, w, nf):
    n = nf + 9
    L = laplacian(edges, w, n)
    A = [L[i][:nf] + [L[i][nf + j] for j in range(9)] for i in range(nf)]
    r = 0
    for col in range(nf):
        p = next((i for i in range(r, nf) if A[i][col] != 0), None)
        assert p is not None, "internal block singular"
        A[r], A[p] = A[p], A[r]
        inv = A[r][col]
        A[r] = [v / inv for v in A[r]]
        for i in range(nf):
            if i != r and A[i][col] != 0:
                f = A[i][col]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        r += 1
    X = [[A[i][nf + j] for j in range(9)] for i in range(nf)]
    S = [[L[nf + i][nf + j] - sum(L[nf + i][k] * X[k][j] for k in range(nf))
          for j in range(9)] for i in range(9)]
    return {(i, j): -S[i][j] for i in range(9) for j in range(i + 1, 9)}, S


def ldl_positive(M, kappa):
    n = len(M)
    A = [row[:] for row in M]
    for i in range(n):
        A[i][i] += kappa
    piv = []
    for k in range(n):
        p = A[k][k]
        if p <= 0:
            return False, piv + [p]
        piv.append(p)
        Ak = A[k]
        for i in range(k + 1, n):
            f = A[i][k] / p
            if f:
                Ai = A[i]
                for j in range(k + 1, n):
                    Ai[j] -= f * Ak[j]
    return True, piv


def build_M(q, U):
    c = 1 - 2 * U * U
    cs = [F(1), c]
    for d in range(2, 5):
        cs.append(2 * c * cs[-1] - cs[-2])
    M = [[F(0)] * 9 for _ in range(9)]
    for (i, j), qq in q.items():
        d = min(j - i, 9 - (j - i))
        v = 2 * qq * cs[d]
        M[i][i] += v
        M[j][j] += v
        M[i][j] -= v
        M[j][i] -= v
    return M, cs


# ---------------------------------------------------------------- audit
def audit(cert_path: Path, verbose=True):
    cert = json.loads(Path(cert_path).read_text(encoding="utf-8"))
    name = Path(cert_path).stem.replace("network-certified-", "")
    rep = {"name": name, "path": str(Path(cert_path).relative_to(N12.parent.parent)),
           "blocks": cert["blocks"], "kappa": cert["kappa"], "checks": {}, "numbers": {}}
    chk = rep["checks"]
    t0 = time.time()

    faces = [tuple(f) for f in cert["faces"]]
    nsites, nf, edges = build_graph(faces)
    rec = [tuple(e) for e in cert["edges"]]
    chk["face_mapping_edge_list_identical"] = (edges == rec)
    chk["anchor_edges_i_to_sites_i_and_i+1"] = all(
        (nf + i, i) in edges and (nf + i, (i + 1) % 9) in edges for i in range(9))
    chk["node_count_consistent"] = (nf == nsites + len(faces)) and \
        (len(edges) == 18 + 3 * len(faces)) and (len(faces) == len(cert["faces"]))

    w = [F(s) for s in cert["rational_weights"]]
    chk["weights_positive_normalized"] = (len(w) == len(edges) and all(x > 0 for x in w)
                                          and sum(w) == 1)
    prop = EV / ("network-minimax-" + name + ".json")
    if prop.exists():
        pj = json.loads(prop.read_text(encoding="utf-8"))
        raw = [max(1, round(float(x) * 10 ** 10)) for x in pj["weights"]]
        chk["weights_reproduce_rounding_rule"] = (
            [F(x, sum(raw)) for x in raw] == w if len(raw) == len(w) else False)

    q1, piv1, err1 = schur_inplace(edges, w, nf)
    chk["dirichlet_pivots_positive_exact"] = (err1 is None)
    if err1:
        chk["error"] = str(err1)
        return rep
    q2, S = schur_solve(edges, w, nf)
    chk["schur_two_paths_identical"] = (q1 == q2)
    chk["schur_offdiagonals_nonnegative"] = all(v >= 0 for v in q1.values())
    chk["schur_complement_annihilates_constants"] = all(
        sum(S[i][j] for j in range(9)) == 0 for i in range(9))

    M, cs = build_M(q1, U)
    kappa = F(cert["kappa"])
    psd, piv2 = ldl_positive(M, kappa)
    chk["M_plus_kappa_I_PD_exact"] = psd

    # constants ---------------------------------------------------------------
    mypi = pi_independent()
    rec_pi = (F(cert["constant_intervals"]["pi"][0]), F(cert["constant_intervals"]["pi"][1]))
    chk["independent_pi_inside_recorded_pi"] = (rec_pi[0] <= mypi[0] and mypi[1] <= rec_pi[1])
    Lrec = (F(cert["constant_intervals"]["L"][0]), F(cert["constant_intervals"]["L"][1]))
    s_lo, _ = fp_sin_cos(to_fp(Lrec[0] / 2))
    s_hi, _ = fp_sin_cos(to_fp(Lrec[1] / 2))
    Uf = to_fp(U)
    chk["L_bracket_valid_by_independent_sin"] = bool(s_lo[1] < Uf[0] and Uf[1] < s_hi[0])
    L = Lrec
    D = (9 * L[0] - 2 * mypi[1], 9 * L[1] - 2 * mypi[0])
    chk["D_positive"] = bool(D[0] > 0)
    chk["all_gaps_positive_L_gt_D"] = bool(L[0] - D[1] > 0)
    chk["4L_lt_pi"] = bool(4 * L[1] < mypi[0])
    Lfp = to_fp(L[0]) if L[0] == L[1] else (to_fp(L[0])[0], to_fp(L[1])[1])
    Dfp = (to_fp(D[0])[0], to_fp(D[1])[1])

    # Taylor data -------------------------------------------------------------
    yy = [F(s) for s in cert["simplex_reference"]]
    chk["reference_in_simplex"] = (all(y >= 0 for y in yy) and sum(yy) == 1)
    ycum = [sum(yy[:i]) for i in range(9)]
    theta0 = []
    for i in range(9):
        t = fp_scale(Lfp, F(i))
        if i:
            t = fp_sub(t, fp_scale(Dfp, ycum[i]))
        theta0.append(t)
    chk["reference_gaps_legal"] = all(
        fp_sub(Lfp, fp_scale(Dfp, yy[i]))[0] > 0 for i in range(9))
    E0 = (0, 0)
    g = [(0, 0)] * 9
    for (i, j), qq in q1.items():
        s, c = fp_sin_cos(fp_sub(theta0[i], theta0[j]))
        E0 = fp_add(E0, fp_scale(fp_sub((ONE, ONE), c), 2 * qq))
        g[i] = fp_add(g[i], fp_scale(s, 2 * qq))
        g[j] = fp_sub(g[j], fp_scale(s, 2 * qq))
    lin, nrm = [], []
    for k in range(9):
        dev = [fp_scale(Dfp, ycum[i] - (1 if k < i else 0)) for i in range(9)]
        lin.append(fp_sum(fp_mul(g[i], dev[i]) for i in range(9)))
        nrm.append(fp_sum(fp_mul(dev[i], dev[i]) for i in range(9)))
    lin_min = (min(x[0] for x in lin), min(x[1] for x in lin))
    nrm_max = (max(x[0] for x in nrm), max(x[1] for x in nrm))
    lower = fp_sub(fp_add(E0, lin_min),
                   fp_scale(fp_mul(to_fp(kappa), nrm_max), F(1, 2)))
    ok = lower[0] * U2.denominator > U2.numerator * ONE
    chk["taylor_lower_exceeds_U2"] = bool(ok)
    margin = F(lower[0], ONE) - U2

    # cross-check with recorded numbers --------------------------------------
    def ov(tag, rec_pair):
        r = (F(rec_pair[0]), F(rec_pair[1]))
        mine = {"E0": E0, "linear_min": lin_min, "max_norm2": nrm_max, "lower": lower}[tag]
        m = (F(mine[0], ONE), F(mine[1], ONE))
        return {"recorded": [str(r[0])[:26], str(r[1])[:26]],
                "mine": [str(m[0])[:26], str(m[1])[:26]],
                "overlap": not (m[1] < r[0] or r[1] < m[0]),
                "mine_narrower": bool(r[0] <= m[0] and m[1] <= r[1])}
    rep["crosscheck"] = {}
    for tag, key in (("E0", "energy_at_reference"), ("linear_min", "linear_min"),
                     ("max_norm2", "max_norm2"), ("lower", "lower_energy")):
        rep["crosscheck"][tag] = ov(tag, cert[key])
    rep["numbers"] = {
        "nsites": nsites, "n_faces": len(faces), "n_edges": len(edges),
        "margin_audit": str(margin)[:26],
        "margin_audit_float": float(margin),
        "recorded_margin_float": float(F(cert["margin_lower"])),
        "recorded_margin_matches_lower_minus_U2":
            bool(F(cert["margin_lower"]) == F(cert["lower_energy"][0]) - U2),
        "recorded_lower_lo_gt_U2": bool(F(cert["lower_energy"][0]) > U2),
        "n_dirichlet_pivots": len(piv1), "n_kappa_pivots": len(piv2),
        "cos_constants": [str(x)[:20] for x in cs],
    }
    rep["cpu_s"] = round(time.time() - t0, 2)
    if verbose:
        fails = [k for k, v in chk.items() if v is False]
        print(f"[{name}] blocks={cert['blocks']} kappa={kappa} "
              f"PASS={sum(1 for v in chk.values() if v is True)} "
              f"FAIL={fails if fails else 'none'} "
              f"margin≈{float(margin):.6e} cpu={rep['cpu_s']}s")
        for k in fails:
            print("   FAIL:", k, chk[k])
        for tag, c in rep["crosscheck"].items():
            print(f"   {tag:10s} overlap={c['overlap']} mine_narrower={c['mine_narrower']}")
    return rep


def main():
    args = sys.argv[1:]
    if args and args[0] == "--files":
        paths = [Path(p) for p in args[1:]]
    else:
        names = args or ["234", "225", "117", "126", "135", "144"]
        paths = [EV / f"network-certified-{n}.json" for n in names]
    reports = []
    for p in paths:
        reports.append(audit(p))
    (OUT / "audit-report.json").write_text(
        json.dumps(reports, indent=1, ensure_ascii=False), encoding="utf-8")
    print("\n== summary ==")
    nfail = 0
    for r in reports:
        fails = [k for k, v in r["checks"].items() if v is False]
        nfail += len(fails)
        print(f"{r['name']:>10}  blocks={r['blocks']}  "
              f"checks={sum(1 for v in r['checks'].values() if v is True)}P/"
              f"{len(fails)}F  "
              f"taylor_ok={r['checks'].get('taylor_lower_exceeds_U2')}  "
              f"margin≈{r['numbers'].get('margin_audit_float')}")
    print(f"total FAILs: {nfail}")
    print("log ->", OUT / "audit-report.json")


if __name__ == "__main__":
    main()
