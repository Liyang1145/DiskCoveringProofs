"""Negative tests: the merge verifier must reject every tampering mode.

Builds mutated copies of a real branch file in this directory (never touching
the lead's tree) and checks that merge_branches rejects each one.
"""
import json
import shutil
import sys
from pathlib import Path
from fractions import Fraction as F

import boxlib as BX
from merge_branches import merge, load_plan

HERE = Path(__file__).parent
PLAN = HERE / "stage11825-plan.json"
EV = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\n12-global"
          r"\evidence\parallel-domain")
SRC = EV / "branch-0.json"
WORK = HERE / "selftest"


def problems_for(path, extra=()):
    man = merge(str(PLAN), [str(path)] + [str(p) for p in extra])
    return man["problems"]


def main():
    WORK.mkdir(exist_ok=True)
    base = json.loads(SRC.read_text())
    plan, psha = load_plan(PLAN)
    cases = []

    # 0. control: the untouched file must have NO local problems besides the
    #    (expected) missing-sibling report
    p0 = WORK / "ok.json"
    p0.write_text(json.dumps(base))
    pr = problems_for(p0)
    cases.append(("control (untouched)", pr,
                  all("missing branches" in x for x in pr)))

    # 1. missing metadata (simulates the metadata-write window)
    d = dict(base); d.pop("branch_root")
    p = WORK / "no_root.json"; p.write_text(json.dumps(d))
    pr = problems_for(p)
    cases.append(("missing branch_root", pr,
                  any("branch_root missing" in x for x in pr)))

    # 2. swapped root (another branch's root)
    other = json.loads((EV / "branch-2.json").read_text())
    d = dict(base); d["branch_root"] = other["branch_root"]
    p = WORK / "swapped_root.json"; p.write_text(json.dumps(d))
    pr = problems_for(p)
    cases.append(("swapped branch_root", pr,
                  any("branch_root != plan root" in x for x in pr)))

    # 3. unknown branch id
    d = dict(base); d["branch_id"] = 99
    p = WORK / "unknown_id.json"; p.write_text(json.dumps(d))
    pr = problems_for(p)
    cases.append(("unknown branch id", pr,
                  any("unknown" in x for x in pr)))

    # 4. leaf moved outside the root
    d = json.loads(SRC.read_text())
    H = d["leaves"][0]["H"]
    b = BX.decode(H)
    b2 = list(b); b2[1] = (b[1][1] + F(1, 1000), b[1][1] + F(1, 500))
    d["leaves"][0]["H"] = BX.encode(tuple(b2))
    p = WORK / "leaf_outside.json"; p.write_text(json.dumps(d))
    pr = problems_for(p)
    cases.append(("leaf outside root", pr,
                  any("outside root" in x or "frontier tree" in x for x in pr)))

    # 5. dropped leaf (coverage hole)
    d = json.loads(SRC.read_text()); d["leaves"] = d["leaves"][:-1]
    p = WORK / "dropped_leaf.json"; p.write_text(json.dumps(d))
    pr = problems_for(p)
    cases.append(("dropped leaf (hole)", pr,
                  any("frontier tree" in x or "counts" in x for x in pr)))

    # 6. duplicate leaf (overlap)
    d = json.loads(SRC.read_text()); d["leaves"] = d["leaves"] + [d["leaves"][0]]
    p = WORK / "dup_leaf.json"; p.write_text(json.dumps(d))
    pr = problems_for(p)
    cases.append(("duplicated leaf", pr,
                  any("duplicate" in x or "frontier tree" in x for x in pr)))

    # 7. tampered counts
    d = json.loads(SRC.read_text()); d["counts"]["split"] += 1
    p = WORK / "bad_counts.json"; p.write_text(json.dumps(d))
    pr = problems_for(p)
    cases.append(("tampered split count", pr,
                  any("counts.split" in x for x in pr)))

    # 8. same branch twice
    pr = problems_for(p0, extra=[p0])
    cases.append(("branch supplied twice", pr,
                  any("supplied twice" in x for x in pr)))

    # 9. torn file
    p = WORK / "torn.json"; p.write_text('{"branch_id": 0, "leaves": [')
    pr = problems_for(p)
    cases.append(("torn/unparsable", pr,
                  any("unparsable" in x for x in pr)))

    ok = True
    for name, pr, good in cases:
        ok &= good
        print("%-28s rejected-as-expected=%-5s  problems=%d %s"
              % (name, good, len(pr), pr[:1]))
    print("\nALL NEGATIVE TESTS PASS:", ok)
    shutil.rmtree(WORK, ignore_errors=True)


if __name__ == "__main__":
    main()
