"""Compare my independent enumeration with the stored catalogues (topology-audit-cc2).

All canonicalisation uses canon_true (provably invariant under the full group D_N x S_m,
verified in canon_check.invariance_test).  Reported quantities:
  - distinct canon_true classes of the stored list,
  - how many stored classes are absent from my independently enumerated class set,
  - how many of my classes are absent from the stored list.
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from canon_check import canon_true  # noqa

ROOT = HERE.parents[2]


def load_mine(N, m):
    p = HERE / "evidence" / ("indep-enum-N%d-m%d.json" % (N, m))
    d = json.loads(p.read_text(encoding="utf-8"))
    return [tuple(tuple(f) for f in json.loads(c)) for c in d["classes"]]


def stored_n12():
    p = ROOT / "n12-global" / "members" / "nine-topology" / "graphs.json"
    d = json.loads(p.read_text(encoding="utf-8"))
    return d, [tuple(tuple(f) for f in g["faces"]) for g in d["graphs"]]


def stored_n14(key):
    p = ROOT / "next-cover-global" / "members" / "topology" / "k-catalogue-n14.json"
    d = json.loads(p.read_text(encoding="utf-8"))
    return [tuple(tuple(f) for f in g["faces"]) for g in d[key]]


def corrected(key):
    p = ROOT / "next-cover-global" / "lead" / "k10-catalogue-corrected.json"
    d = json.loads(p.read_text(encoding="utf-8"))
    return [tuple(tuple(f) for f in g["faces"]) for g in d[key]]


def compare(name, N, m, mine, theirs):
    mine = [tuple(tuple(f) for f in g) for g in mine]
    theirs = [tuple(tuple(f) for f in g) for g in theirs]
    ms = set(canon_true(N, m, f) for f in mine)
    ts = set(canon_true(N, m, f) for f in theirs)
    return dict(name=name, N=N, m=m, mine_n=len(mine), mine_classes=len(ms),
                theirs_n=len(theirs), theirs_classes=len(ts),
                theirs_missing_from_mine=len(ts - ms),
                mine_missing_from_theirs=len(ms - ts),
                classes_equal=(ms == ts))


def main():
    rep = {}
    # n12 k9 calibration
    d9, s9 = stored_n12()
    mine9 = load_mine(9, 3)
    rep["n12_k9_m3"] = compare("n12 graphs.json m=3 (51)", 9, 3, mine9,
                               [g for g in s9 if any(v >= 11 for f in g for v in f)])
    # n14 stored lists and the lead's corrected list
    for key, m in (("10/3", 3), ("10/4", 4)):
        mine = load_mine(10, m)
        rep["stored_" + key] = compare("k-catalogue-n14 " + key, 10, m, mine,
                                       stored_n14(key))
        rep["corrected_" + key] = compare("k10-catalogue-corrected " + key, 10, m, mine,
                                          corrected(key))
    (HERE / "evidence" / "compare-stored.json").write_text(
        json.dumps(rep, indent=1), encoding="utf-8")
    for k, v in rep.items():
        print(k, json.dumps(v))


if __name__ == "__main__":
    main()
