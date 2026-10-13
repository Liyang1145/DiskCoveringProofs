"""Integrity snapshot of n21 proven milestones, explicitly NOT a global proof certificate."""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent
WORKSPACE = ROOT.parent.parent
EV = ROOT/"evidence"
SNAPSHOT = EV/"MILESTONE-SNAPSHOT.json"
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--create",action="store_true")
    args = parser.parse_args()
    root = json.loads((EV/"core-root-verified.json").read_text())
    upper = json.loads((EV/"upper-verified.json").read_text())
    local = json.loads((EV/"local-isolation-verified.json").read_text())
    candidate = json.loads((EV/"candidate-tree-verified.json").read_text())
    core = json.loads((EV/"core-capacity-cut-verified.json").read_text())
    six = json.loads((EV/"six-core-exclusion/REPLAY.json").read_text())
    negative = json.loads((EV/"negative-checks.json").read_text())
    regression = json.loads((EV/"peeling-extended-regression2/SUMMARY.json").read_text())
    assert all(d["verified"] for d in (root,upper,local,candidate,core,six,negative))
    assert all(d.get("global_optimality_proved") is False for d in (root,upper,local,candidate,core,six,negative))
    assert root["root_sha256"] == upper["root_sha256"] == local["root_sha256"] == sha(EV/"core-root.json")
    assert root["dimension"] == 173 and local["positive_leading_principal_minors"] == 92
    assert upper["triangles"] == 53 and upper["covering_radius_equals_core_radius"]
    assert candidate["nodes"] == 4817 and candidate["counts"] == {"SPLIT":2408,"DUAL":2249,"LOCAL":160}
    assert candidate["tree_sha256"] == sha(EV/"candidate-tree-round2.json.gz")
    assert six["n21_maximum_boundary_cells"] == 14 and core["maximum_boundary_cells"] == 15
    assert regression["verified_small_regressions"] and regression["node_limit_rejected"]
    assert any(r["I"] == 9 and r["B"] == 3 for r in regression["tests"])
    if args.create:
        assert not SNAPSHOT.exists(), "Do not overwrite a fixed milestone snapshot"
        files = {p for p in ROOT.iterdir() if p.is_file() and p.suffix in (".py",".cpp",".md")}
        files |= {EV/p for p in ("candidate-dec17.json","candidate-numeric.json","kkt-numeric.json",
                  "core-system.json","core-root.json","core-root-verified.json","upper-verified.json",
                  "angle-constants.json","local-isolation-verified.json","core-capacity-cut-verified.json",
                  "candidate-tree-round1.json.gz","candidate-tree-round2.json.gz",
                  "candidate-tree-verified.json","negative-checks.json")}
        for folder in ("six-core-exclusion","peeling-round1","peeling-round2-high",
                       "peeling-round3-middle","peeling-extended-regression2"):
            files |= {p for p in (EV/folder).iterdir() if p.is_file()}
        files |= {ROOT.parent/"n13-global/independent_checks.py",
                  ROOT.parent/"disk-cover-proof-library/LOCAL-VS-GITHUB-11-12-14.md"}
        upstream = ROOT.parent/"disk-cover-proof-library/external/pinned/cover20/proof_bundle"
        files |= {upstream/p for p in ("discovery/discover20.py","discovery/force20.py",
                                      "core/compact_force20.py","core/exact_arcs.py")}
        record = {"date":"2026-10-03","timezone":"Asia/Shanghai","N":21,"global_optimality_proved":False,
                  "proven_milestones":["isolated core root","same-root whole-disk upper cover",
                    "92D anchor-only core isolation","candidate-topology full angle lower bound",
                    "elementary core count cut","six-disk auxiliary strict lower bound",
                    "unpruned regression through nine interior vertices"],
                  "remaining_families":[[12,9],[13,8],[14,7]],
                  "remaining_obligations":["complete enumeration of remaining three families",
                      "exclude all noncandidate survivor continuous domains",
                      "final arbitrary-cover and catalogue/interface audit"],
                  "files":{p.relative_to(WORKSPACE).as_posix():sha(p) for p in sorted(files)}}
        SNAPSHOT.write_text(json.dumps(record,indent=2),encoding="utf8")
    record = json.loads(SNAPSHOT.read_text())
    assert record["global_optimality_proved"] is False
    for name,expected in record["files"].items():
        assert sha(WORKSPACE/name) == expected, ("milestone changed",name)
    print(json.dumps({"verified_integrity":True,"bound_files":len(record["files"]),
                      "global_optimality_proved":False,"snapshot_sha256":sha(SNAPSHOT)},indent=2))


if __name__ == "__main__":
    main()
