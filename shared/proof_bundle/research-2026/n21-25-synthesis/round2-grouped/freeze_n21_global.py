"""Bind the complete written n21 theorem and its accepted evidence chain."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent
SYN = ROOT.parent
WORK = SYN.parent.parent
EV = ROOT / "evidence"
assert __debug__


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(path.read_text(encoding="utf8"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    files = set()
    # Read and preserve both immutable milestone manifests and every input
    # they bind.  No claim is inferred merely from an old completion flag.
    for snap in (SYN / "evidence/JOINT-MILESTONE-SNAPSHOT.json",
                 SYN.parent / "n21-global/evidence/MILESTONE-SNAPSHOT-v2.json"):
        files.add(snap)
        for rel, digest in read(snap)["files"].items():
            path = WORK / rel
            assert sha(path) == digest, ("changed immutable input", rel)
            files.add(path)
    interface = EV / "n21-interfaces-resume2"
    assert read(interface / "INTERFACES.json")["verified"]
    root = read(interface / "core-root-verified.json")
    upper = read(interface / "upper-verified.json")
    local = read(interface / "local-isolation-verified.json")
    angle = read(interface / "n21-core-angle-replayed.json")
    six = read(interface / "six-core-exclusion/REPLAY.json")
    assert all(r["verified"] for r in (root, upper, local, angle, six))
    assert root["dimension"] == 173
    assert root["root_sha256"] == upper["root_sha256"] == local["root_sha256"]
    assert root["root_sha256"] == sha(interface / "core-root.json")
    assert upper["covering_radius_equals_core_radius"] and upper["triangles"] == 53
    assert local["positive_leading_principal_minors"] == 92
    assert angle["tree_sha256"] == sha(SYN / "evidence/n21-positive-core-angle-tree.json.gz")
    assert angle["nodes"] == 4939
    assert angle["counts"] == {"SPLIT": 2469, "DUAL": 2312, "LOCAL": 158}
    assert six["topology_orbits"] == 3 and F(six["radius"]) == F(2771, 5000)
    assert F(six["strict_core_ratio_gap"]) > 0
    area = read(EV / "n21-B12-lens-area-resume1.json")
    assert area["verified"] and F(area["area_contradiction_margin"]) > 0
    assert read(EV / "partial-force-negative-checks-resume1.json")["verified"]
    files |= {p for p in interface.rglob("*") if p.is_file()}
    files |= {ROOT / name for name in ("N21-GLOBAL-PROOF.md", "partial_force_exact.py",
              "replay_hierarchy.py", "audit_bindings.py", "replay_n21_interfaces.py",
              "negative_force_checks.py", "freeze_n21_global.py")}
    files |= {EV / name for name in ("n21-B12-lens-area-resume1.json",
              "partial-force-negative-checks-resume1.json")}
    totals = {}
    for B, expected, core in ((13, 583857, 30), (14, 745290, 0)):
        auditpath = EV / f"B{B}-hierarchy-embedding-audit-resume1.json"
        audit = read(auditpath)
        assert audit["verified"] and audit["coverage_partition_complete"]
        assert audit["catalog_types"] == expected and not audit["pending_catalog_indices"]
        assert audit["strict_exclusion_types"] == expected-core
        assert audit["core_lower_bound_cases"] == core
        assert audit["source_sha256"] == sha(ROOT / "audit_bindings.py")
        files.add(auditpath)
        datasets = (f"B{B}-pair-full", f"B{B}-outer-refinement", f"B{B}-full-refinement")
        receipts = (EV / f"B{B}-pair-root-force/SUMMARY.json",
                    EV / f"B{B}-outer-combined.json", EV / f"B{B}-full-combined-resume1.json")
        replays = (EV / f"B{B}-pair-replay-standalone.json",
                   EV / f"B{B}-replay-standalone.json", EV / f"B{B}-full-replay-standalone.json")
        for stage, dataset, receiptpath, replaypath in zip(audit["stages"], datasets, receipts, replays):
            grouppath = EV / dataset / "GROUPS.json"
            receipt, replay = read(receiptpath), read(replaypath)
            assert replay["verified"] and F(replay["minimum_margin"]) > 0
            assert replay["groups_sha256"] == sha(grouppath) == stage["groups_sha256"]
            assert replay["combined_sha256"] == sha(receiptpath)
            assert stage["replay_sha256"] == sha(replaypath)
            files |= {grouppath, receiptpath, replaypath}
            for row in receipt["outcomes"]:
                if row["status"] == "excluded":
                    path = (ROOT / row["certificate_path"] if "certificate_path" in row else
                            receiptpath.parent / f"group-{row['group']:07}.json.gz")
                    assert sha(path) == row["tree_sha256"]
                    files.add(path)
        totals[str(B)] = {"strict_excluded": expected-core, "core_lower_bound": core, "pending": 0}
    manifest = {
        "schema": "n21-unrestricted-written-and-exact-certificate-proof-v1",
        "date": "2026-10-03", "timezone": "Asia/Shanghai",
        "N": 21, "global_optimality_source_proof_completed": True,
        "written_arbitrary_cover_and_peeling_argument": "N21-GLOBAL-PROOF.md",
        "mathematical_argument_is_not_machine_formalized": True,
        "formalization_completed": False, "third_party_peer_review_completed": False,
        "r_strict_interval": root["r_strict_interval"], "type_closure": totals,
        "remaining_five_target_global_proofs": [25, 22, 23, 24],
        "files": {p.relative_to(WORK).as_posix(): sha(p) for p in sorted(files)},
    }
    args.output.write_text(json.dumps(manifest, indent=2), encoding="utf8")
    for rel, digest in read(args.output)["files"].items():
        assert sha(WORK / rel) == digest
    print("N21 unrestricted SOURCE proof chain bound:", len(files), "files; five-target goal remains active", flush=True)


if __name__ == "__main__":
    main()
