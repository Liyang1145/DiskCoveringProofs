"""Terminal provenance check: are the 8 C1366 cuts (a) already present in the PREVIOUS domain
and (b) contributed by the FULLY CLOSED cases of the final round?

Round-8 audit results: case0 [0],11/512,+1 has pending [] (closed, 1 leaf, 0 open);
case2 [0,1],65/256,+1 has pending [] (closed, 3 leaves, 0 open); cases 1 and 3 have nonempty
pending lists and contribute NO cuts (the audit only adds a cut when `pending` is empty).
Also verifies the coefficient identity sum_i coeff_{j,i} = 4.5-j and sum_j coeff_{j,i} = 0.
"""
import json
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAD = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead")


def norm(c):
    return (tuple(sorted(c["indices"])), c["sense"], str(c["fraction_of_total"]))


def cuts_of(p):
    d = json.loads(p.read_text(encoding="utf-8"))
    lst = d.get("cuts") or []
    # c1366 stores cuts as [{cut:{...},before,after}]
    out = []
    for c in lst:
        if "cut" in c:
            out.append(norm(c["cut"]))
        else:
            out.append(norm(c))
    return out


def main():
    out = {}
    c1365 = cuts_of(LEAD / "q10-c1365-domain.json")
    c1366 = cuts_of(LEAD / "q10-c1366-domain.json")
    out["n_cuts_c1365"] = len(c1365)
    out["n_cuts_c1366"] = len(c1366)
    out["c1365_cuts"] = [[list(i), s, t] for i, s, t in c1365]
    out["new_cuts_in_c1366"] = [[list(i), s, t] for i, s, t in c1366
                                if (i, s, t) not in set(c1365)]
    # round 8 audit: which cases are fully closed (pending empty) and what they would emit
    a = json.loads((LEAD / "q10-metric-round8-audit.json").read_text(encoding="utf-8"))
    files = sorted(LEAD.glob("q10-metric-round8-*.json"))
    closed_cases = []
    for f in files:
        if f.name == "q10-metric-round8-audit.json" or f.name.endswith("-config.json"):
            continue
        d = json.loads(f.read_text(encoding="utf-8"))
        if d.get("pending") == []:
            closed_cases.append((f.name, d.get("case")))
    out["round8_fully_closed_cases"] = closed_cases
    out["round8_declared_cuts"] = [[list(i), s, t] for i, s, t in [norm(c) for c in a["cuts"]]]
    # cuts that round 8's closed cases can justify (their own cut planes)
    just = []
    for name, case in closed_cases:
        ids, t, sgn = case
        sense = "less" if sgn == 1 else "greater"
        just.append((tuple(sorted(ids)), sense, str(t)))
    out["cuts_justified_by_round8_closed_cases"] = [[list(i), s, t] for i, s, t in just]
    out["all_c1366_cuts_justified_round8"] = all(c in set(just) for c in c1366)
    out["all_new_c1366_cuts_justified"] = all(c in set(just) for c in c1366
                                              if c not in set(c1365))
    # coefficient identities
    N = 10
    rows = [[Q(9 - i, 10) - (1 if i < j else 0) for i in range(N)] for j in range(N)]
    out["row_sums_4p5_minus_j"] = [str(sum(r)) for r in rows]
    out["col_sums_zero"] = [str(sum(rows[j][i] for j in range(N))) for i in range(N)]
    out["col_sums_all_zero"] = all(sum(rows[j][i] for j in range(N)) == 0 for i in range(N))
    out["total_sum"] = str(sum(sum(r) for r in rows))
    (HERE / "terminal-provenance.json").write_text(json.dumps(out, indent=1), encoding="utf-8")
    for k, v in out.items():
        print(k, ":", json.dumps(v)[:400])


if __name__ == "__main__":
    main()
