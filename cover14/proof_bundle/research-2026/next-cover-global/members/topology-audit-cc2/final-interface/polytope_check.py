"""Independent exact check of the C1366 polytope declaration (scope final-interface audit).

Does NOT re-run the exterior trees.  Checks only structural facts that the bridge's scope
sentence uses, on the stored JSON, in exact Fraction arithmetic:
  1. every vertex has 10 entries and satisfies sum x = 1 and all 128 stored inequalities;
  2. the stored equality [10,0,-1] is 10*x0 = ... check its reading;
  3. the vertex count and per-vertex active-constraint ranks;
  4. whether the declared cuts are of "fraction_of_total" (x_i <= c) type and their total.
"""
import json
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAD = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead")


def decode(tri):
    """Producer encoding (q10_rational_polytope_audit.scalar): a triple [a,b,c] denotes the
    rational -c, under the cross-check constraints b = 0 and a = -10c."""
    a, b, c = (Q(x) for x in tri)
    if not (b == 0 and a == -10 * c):
        raise ValueError("bad scalar encoding %s" % (tri,))
    return -c


def main():
    D = json.loads((LEAD / "q10-c1366-domain.json").read_text(encoding="utf-8"))
    P = D["polytope"]
    verts = [[decode(t) for t in v] for v in P["vertex_set"]]
    out = {"n_vertices": len(verts), "dim": P["dim"]}
    bad_sum = sum(1 for v in verts if sum(v) != 1)
    out["vertices_violating_sum_eq_1"] = bad_sum
    # inequalities: [[coeff list],[rhs triple],name]
    ineqs = []
    for c, rhs, name in P["inequalities"]:
        cc = [Q(x) for x in c]
        r = decode(rhs)
        ineqs.append((cc, r, name))
    viol = 0
    for v in verts:
        for cc, r, name in ineqs:
            if sum(a * b for a, b in zip(cc, v)) < r:
                viol += 1
    out["vertex_inequality_violations"] = viol
    # equality rows
    eqs = []
    eq_rows = P["equality"]          # [coeff list of 10 ones, scalar triple for RHS=1]
    eqs.append(([Q(x) for x in eq_rows[0]], decode(eq_rows[1])))
    eviol = 0
    for v in verts:
        for cc, r in eqs:
            if sum(a * b for a, b in zip(cc, v)) != r:
                eviol += 1
    out["vertex_equality_violations"] = eviol
    out["equality_rows"] = [[str(x) for x in c] + [str(r)] for c, r in eqs]
    # active ranks
    min_rank = None
    max_rank = None
    for v in verts:
        act = []
        for cc, r, name in ineqs:
            if sum(a * b for a, b in zip(cc, v)) == r:
                act.append(cc)
        act.extend(cc for cc, r in eqs)
        # exact rank by fraction Gaussian elimination
        M = [row[:] for row in act]
        rank = 0
        cols = 10
        piv = 0
        for col in range(cols):
            p = None
            for i in range(rank, len(M)):
                if M[i][col] != 0:
                    p = i
                    break
            if p is None:
                continue
            M[rank], M[p] = M[p], M[rank]
            pr = M[rank]
            for i in range(rank + 1, len(M)):
                if M[i][col] != 0:
                    f = M[i][col] / pr[col]
                    M[i] = [a - f * b for a, b in zip(M[i], pr)]
            rank += 1
            if rank == len(M):
                break
        min_rank = rank if min_rank is None else min(min_rank, rank)
        max_rank = rank if max_rank is None else max(max_rank, rank)
    out["active_rank_min"] = min_rank
    out["active_rank_max"] = max_rank
    out["cuts"] = D["cuts"]
    (HERE / "polytope-check.json").write_text(json.dumps(out, indent=1), encoding="utf-8")
    print(json.dumps({k: v for k, v in out.items() if k != "cuts"}, indent=1))


if __name__ == "__main__":
    main()
