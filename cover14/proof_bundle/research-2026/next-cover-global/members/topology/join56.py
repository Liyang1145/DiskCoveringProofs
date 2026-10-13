"""Complete graph-isomorphism join: n14 generator calibration (N=9, m<=3) against the n12 56 catalogue.

Scope: research-2026/next-cover-global/members/topology/.  Integer only.  Same count is not sufficient:
this checks that the two 56-element family of labelled triangulated disks are isomorphic as structures
(ring rotation N=9, reflection, hub relabeling), i.e. a perfect matching exists.
"""
import json
from collections import Counter
from pathlib import Path

import gen_k10_catalogue as G

HERE = Path(__file__).resolve().parent
N = 9
N12 = Path(__file__).resolve().parents[3] / "n12-global" / "members" / "nine-topology" / "graphs.json"


def key_of(m, faces):
    return G.full_canon(N, m, [tuple(f) for f in faces])


def main():
    mine = json.loads((HERE / "k-catalogue-calib.json").read_text(encoding="utf-8"))
    old = json.loads(N12.read_text(encoding="utf-8"))["graphs"]
    my_by_m = Counter()
    my_keys = {}
    for m_s, entries in mine.items():
        m = int(m_s.split("/")[1])
        for e in entries:
            k = key_of(m, e["faces"])
            my_by_m[m] += 1
            my_keys.setdefault((m, k), []).append("calib:%s" % e.get("skeleton", "?"))
    old_by_m = Counter()
    old_keys = {}
    for e in old:
        m = e["m"]
        k = key_of(m, e["faces"])
        old_by_m[m] += 1
        old_keys.setdefault((m, k), []).append("n12:%s" % e["id"])
    print("calibration per m:", dict(my_by_m))
    print("n12 catalogue per m:", dict(old_by_m))
    only_mine = sorted(set(my_keys) - set(old_keys))
    only_old = sorted(set(old_keys) - set(my_keys))
    print("keys only in calibration:", len(only_mine))
    print("keys only in n12:", len(only_old))
    matched = 0
    for k in sorted(set(my_keys) & set(old_keys)):
        matches = [(a, b) for a in my_keys[k] for b in old_keys[k]]
        matched += 1
        if matched <= 8:
            print("JOIN m=%d  %s  <->  %s" % (k[0], my_keys[k], old_keys[k]))
    print("isomorphic keys matched:", matched, " total calibration:", sum(my_by_m.values()),
          " total n12:", sum(old_by_m.values()))
    assert not only_mine and not only_old
    assert sum(my_by_m.values()) == sum(old_by_m.values()) == 56
    assert matched == 56
    print("PERFECT ISOMORPHISM JOIN: 56 <-> 56 OK")


if __name__ == "__main__":
    main()
