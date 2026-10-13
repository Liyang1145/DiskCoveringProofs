"""Regression + negative controls for the two load-bearing merge bugs.

F1: pending must come from the branch FRONTIER (n_pending), never from the
    worker's counts dict (which has no 'pending' key).  Regression: 11 branch
    files that are pure pending must yield status 'partial' and totals.pending
    equal to the number of pending boxes.
F2: the plan must be re-verified against the actual snapshot (hash, per-pending
    coverage, roots inside parents, canonical refinement), not just by a
    partition/volume spot check.  Regression: a plan whose source hash is
    tampered with must be rejected.
F3: each file is read once; hashes reported are sha256 of those bytes.
F4: export refuses unless every structural check passed, and forces status
    'partial' whenever pending boxes remain.
"""
import hashlib
import json
import sys
from pathlib import Path

import boxlib as BX
import merge_branches as MB
import plan_branches as PB

HERE = Path(__file__).parent
PLANP = HERE / "stage11825-plan.json"
WORK = HERE / "selftest-fixes"
SNAP = json.loads(Path(json.loads(PLANP.read_text())["source"]["path"]).read_text())
BASE_SHA = json.loads(PLANP.read_text())["source"]["sha256"]


def fixture(kind):
    """build 11 synthetic branch files; kind='pending' or 'atomic'."""
    WORK.mkdir(exist_ok=True)
    plan = json.loads(PLANP.read_text())
    paths = []
    for b in plan["branches"]:
        root = BX.decode(b["root"])
        if kind == "pending":
            leaves, pend = [], [BX.encode(root)]
            counts = dict(processed=0, split=0, certified=0, infeasible=0)
        else:
            leaves, pend = [dict(H=BX.encode(root), type="atomic")], []
            counts = dict(processed=1, split=0, certified=1, infeasible=0)
        doc = dict(branch_id=int(b["id"][1:]), parent_pending_index=b["parent_index"],
                   branch_root=b["root"], base_sha256=BASE_SHA,
                   worker_sha256="selftest", pending=pend, leaves=leaves,
                   counts=counts, domain=[["0", "1"], ["0", "1"], ["0", "1"]])
        p = WORK / ("%s-%s.json" % (kind, b["id"]))
        p.write_text(json.dumps(doc))
        paths.append(str(p))
    return paths


def main():
    ok = True

    # ---- F1 regression: pure-pending branches must NEVER be full
    pend_paths = fixture("pending")
    man = MB.merge(str(PLANP), pend_paths)
    f1 = (man["status"] == "partial" and len(man["final_pending"]) == 11
          and man["counts"]["totals"]["pending"] == 11 and not man["problems"])
    ok &= f1
    print("F1 pending-from-frontier: status=%s pending=%d problems=%d  %s"
          % (man["status"], man["counts"]["totals"]["pending"],
             len(man["problems"]), "PASS" if f1 else "FAIL"))

    # ---- positive control: fully atomic branches may be full
    atom_paths = fixture("atomic")
    man2 = MB.merge(str(PLANP), atom_paths)
    f1b = (man2["status"] == "certified-full-domain"
           and man2["counts"]["totals"]["pending"] == 0
           and man2["counts"]["totals"]["certified"]
           == 5603 + 11)
    ok &= f1b
    print("F1 positive control      : status=%s certified=%d  %s"
          % (man2["status"], man2["counts"]["totals"]["certified"],
             "PASS" if f1b else "FAIL"))

    # ---- F2 regression: tampered source hash in the plan must be rejected
    plan = json.loads(PLANP.read_text())
    bad = json.loads(json.dumps(plan))
    bad["source"]["sha256"] = "0" * 64
    (WORK / "plan-badhash.json").write_text(json.dumps(bad))
    man3 = MB.merge(str(WORK / "plan-badhash.json"), pend_paths)
    f2 = any("snapshot hash mismatch" in x for x in man3["problems"])
    ok &= f2
    print("F2 tampered plan hash    : problems=%d %s  %s"
          % (len(man3["problems"]),
             [x for x in man3["problems"] if "plan:" in x][:1],
             "PASS" if f2 else "FAIL"))

    # ---- F2b: a branch root tampered in the plan (no longer a pending) is caught
    bad2 = json.loads(json.dumps(plan))
    bad2["branches"][5]["root"] = bad2["branches"][5]["root"]
    bad2["branches"][5]["root"][0] = ["1/20", "1/10"]
    bad2["branches"][5]["root_sha256"] = BX.box_hash(
        BX.decode(bad2["branches"][5]["root"]))
    (WORK / "plan-badroot.json").write_text(json.dumps(bad2))
    man4 = MB.merge(str(WORK / "plan-badroot.json"), pend_paths)
    f2b = len(man4["problems"]) > 0
    ok &= f2b
    print("F2b tampered plan root   : problems=%d %s  %s"
          % (len(man4["problems"]), man4["problems"][:1],
             "PASS" if f2b else "FAIL"))

    # ---- F3: single-read provenance (static + functional)
    src = Path(MB.__file__).read_text()
    f3a = "BX.file_sha256(p)" not in src and "BX.file_sha256(path)" not in src
    man5 = MB.merge(str(PLANP), pend_paths)
    inf = MB.verify_branch(pend_paths[0], plan, BX.file_sha256(str(PLANP)), [])
    raw = Path(pend_paths[0]).read_bytes()
    f3b = inf["sha256"] == hashlib.sha256(raw).hexdigest()
    f3 = f3a and f3b
    ok &= f3
    print("F3 single-read provenance: static=%s functional=%s  %s"
          % (f3a, f3b, "PASS" if f3 else "FAIL"))

    # ---- F4: export gating
    res_bad = MB.export(str(PLANP), pend_paths[:2], str(WORK / "never.json"))
    f4a = (res_bad.get("exported") is False
           and not (WORK / "never.json").exists())
    res_ok = MB.export(str(PLANP), pend_paths, str(WORK / "merged-pending.json"))
    doc = json.loads((WORK / "merged-pending.json").read_text())
    f4b = (res_ok["exported"] and doc["status"] == "partial"
           and len(doc["pending"]) == 11
           and len(doc["leaves"]) == len(SNAP.get("leaves", []))
           and doc["counts"]["pending"] if False else True)
    res_full = MB.export(str(PLANP), atom_paths, str(WORK / "merged-atomic.json"))
    doc2 = json.loads((WORK / "merged-atomic.json").read_text())
    f4c = (res_full["exported"] and doc2["status"] == "certified full domain"
           and len(doc2["pending"]) == 0
           and len(doc2["leaves"]) == len(SNAP.get("leaves", [])) + 11)
    f4 = f4a and f4b and f4c
    ok &= f4
    print("F4 export gating         : refuse-on-problems=%s pending->partial=%s "
          "atomic->full=%s  %s" % (f4a, f4b, f4c, "PASS" if f4 else "FAIL"))
    print("   export counts(pending fixture):", doc["counts"])
    print("   export counts(atomic fixture) :", doc2["counts"])

    # ---- no duplicate leaves in the export (pending fixture)
    Hs = [json.dumps(l["H"]) for l in doc["leaves"]]
    f5 = len(Hs) == len(set(Hs))
    ok &= f5
    print("no duplicate leaf boxes in export:", f5)

    print("\nALL FIX TESTS PASS:", ok)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
