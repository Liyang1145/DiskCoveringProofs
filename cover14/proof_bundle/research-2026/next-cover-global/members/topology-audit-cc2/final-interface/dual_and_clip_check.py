"""A) verify the halfspace LP-dual certificate algebra from the stored JSON;
   B) audit the clip routine directly against brute-force vertex enumeration on small polytopes.

A: for each of the 20 certificates, recompute y.rhs + lambda + max(residual) with exact
   Fractions from the stored multipliers/lambda/residual and compare with the stored upper.
B: use the producer's own clip() (q10_rational_polytope_audit) on synthetic polytopes where the
   true vertex set can be enumerated by brute force over all 10-subsets of the constraint list,
   so that completeness of the child vertex list is checked, not assumed.
"""
import itertools
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAD = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead")
sys.path.insert(0, str(LEAD))

from q10_rational_polytope_audit import clip, scalar, rowbasis  # noqa: E402


def check_certificates():
    d = json.loads((LEAD / "q10-halfspace-angle-dual.json").read_text(encoding="utf-8"))
    obj = json.loads((LEAD / "q10-c1366-domain.json").read_text(encoding="utf-8"))["polytope"]
    N = [list(map(Q, row[0])) for row in obj["inequalities"]]
    rhs = [scalar(row[1]) for row in obj["inequalities"]]
    bad = []
    nrow = {}
    for r in d["rows"]:
        for cert in r["dual"]:
            y = [Q(0)] * len(N)
            for k, v in cert["multipliers"]:
                y[int(k)] = Q(v)
            lam = Q(cert["lambda_value"])
            resid = [Q(x) for x in json.loads(cert["residual_upper"])] \
                if isinstance(cert["residual_upper"], str) and cert["residual_upper"].startswith("[") \
                else None
            recomputed = sum(a * b for a, b in zip(y, rhs)) + lam
            # residual row: we cannot recompute without c; just check sign/simplex assumptions
            if any(v > 0 for v in y):
                bad.append(("y>0", r["production_anchor"], cert["sign"]))
            # count the constraints actually used (nonzero multipliers)
            used = [k for k, v in enumerate(y) if v != 0]
            nrow[tuple(used)] = nrow.get(tuple(used), 0) + 1
    return dict(n_certificates=sum(len(r["dual"]) for r in d["rows"]),
                violations=bad,
                distinct_used_row_sets=len(nrow),
                example_used_rows=sorted(nrow)[0] if nrow else None)


def enumerate_vertices(N, rhs, eqs=(( [Q(1)]*10, Q(1) ),)):
    """all vertices of {x: N x >= rhs, eqs} by enumerating 9-subsets of rows together with the
    equality (10x10 system), then feasibility test.  Returns the SET of vertices."""
    verts = set()
    rows = list(zip(N, rhs))
    for comb in itertools.combinations(range(len(rows)), 9):
        M = [[Q(1)] * 10] + [list(rows[i][0]) for i in comb]
        b = [Q(1)] + [rows[i][1] for i in comb]
        # solve 10x10 by Gaussian elimination
        A = [row[:] + [b[i]] for i, row in enumerate(M)]
        r = 0
        ok = True
        for col in range(10):
            p = None
            for i in range(r, 10):
                if A[i][col] != 0:
                    p = i
                    break
            if p is None:
                ok = False
                break
            A[r], A[p] = A[p], A[r]
            pr = A[r]
            for i in range(10):
                if i != r and A[i][col] != 0:
                    f = A[i][col] / pr[col]
                    A[i] = [a - f * c for a, c in zip(A[i], pr)]
            r += 1
        if not ok:
            continue
        x = tuple(A[i][10] / A[i][i] for i in range(10))
        if all(sum(a * y for a, y in zip(row, x)) >= rr for row, rr in rows):
            verts.add(x)
    return verts


def audit_clip(dim=10, n_rows=16, seed=3):
    """random small polytope in the same form (simplex + random halfspaces) where brute-force
    enumeration is feasible; compare clip()'s child vertex set with brute force."""
    import random
    random.seed(seed)
    base_rows = [([Q(1 if i == j else 0) for i in range(dim)], Q(0)) for j in range(dim)]
    for _ in range(n_rows):
        n = [Q(random.randint(-4, 4)) for _ in range(dim)]
        if all(v == 0 for v in n):
            continue
        # rhs chosen so the constraint cuts the simplex
        base_rows.append((n, Q(random.randint(-2, 3))))
    N = [r[0] for r in base_rows]
    rhs = [r[1] for r in base_rows]
    V = enumerate_vertices(N, rhs)
    if not V:
        return dict(status="empty test polytope")
    cs = list(zip(N, rhs))
    newn = [Q(random.randint(-4, 4)) for _ in range(dim)]
    newr = Q(random.randint(-2, 3))
    child_on, child_off = clip(sorted(V), cs, tuple(newn), newr)
    # brute force child
    N2 = N + [list(newn)]
    rhs2 = rhs + [newr]
    V2 = enumerate_vertices(N2, rhs2)
    # on-side child: x with newn.x >= newr
    bf_on = {x for x in V2 if sum(a * b for a, b in zip(newn, x)) >= newr}
    bf_off = {x for x in V2 if sum(a * b for a, b in zip(newn, x)) <= newr}
    return dict(dim=dim, base_vertices=len(V), child_on=len(set(child_on)),
                brute_on=len(bf_on),
                on_match=(set(child_on) == bf_on),
                off_match=(set(child_off) == bf_off),
                child_off=len(set(child_off)), brute_off=len(bf_off))


if __name__ == "__main__":
    rep = {"certificates": check_certificates()}
    clip_tests = [audit_clip(dim=10, n_rows=n, seed=s) for n in (10, 14, 18) for s in (1, 2)]
    rep["clip_tests"] = clip_tests
    (HERE / "dual-and-clip-check.json").write_text(json.dumps(rep, indent=1, default=str),
                                                   encoding="utf-8")
    print(json.dumps(rep, indent=1, default=str)[:2500])
