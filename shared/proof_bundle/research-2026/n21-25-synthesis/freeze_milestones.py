"""Bind achieved joint research evidence; NEVER mark the five global goals complete."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import hashlib
import json

ROOT=Path(__file__).resolve().parent
WORKSPACE=ROOT.parent.parent
EV=ROOT/"evidence"
SNAPSHOT=EV/"JOINT-MILESTONE-SNAPSHOT.json"
if not __debug__:
    raise RuntimeError("Assertions must be enabled")


def sha(path):
    h=hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda:stream.read(1<<20),b""):
            h.update(block)
    return h.hexdigest()


def validate():
    for n,dimension,geometry in ((22,252,126),(23,234,120),(24,219,114)):
        folder=EV/f"n{n}"
        root=json.loads((folder/"algebraic-check1/root-verified.json").read_text())
        upper=json.loads((folder/"algebraic-check1/upper-verified.json").read_text())
        local=json.loads((folder/"local-isolation-certificate.json").read_text())
        assert all(x["verified"] and x["global_optimality_proved"] is False for x in (root,upper,local))
        assert root["D"]==dimension and root["G"]==local["geometry_dimension"]==geometry
        assert root["root_sha256"]==upper["root_sha256"]==local["root_sha256"]==sha(folder/"core-root.json")
        assert upper["same_core_root_entire_disk_upper"] and upper["cover_radius_equals_core_radius"]
        assert local["positive_leading_principal_minors"]==geometry and F(local["isolation_margin"])>0
    algebraic=json.loads((EV/"n25-algebraic-upper-round2/VERIFIED.json").read_text())
    stress=json.loads((EV/"n25-core-analysis-stable3/stress-verified.json").read_text())
    family=json.loads((EV/"n25-core-analysis-stable3/homothetic-family-optimum-verified.json").read_text())
    assert all(x["verified"] and x["global_optimality_proved"] is False for x in (algebraic,stress,family))
    assert algebraic["triangles"]==64 and algebraic["center_faces"]==32 and algebraic["actual_cover_radius_equals_r"]
    assert stress["positive_rods"]==128 and stress["D8_invariant_stress_free_dimension"]==0
    assert stress["orbit_stationarity_rank"]==10 and stress["all_node_forces_zero"]
    area=json.loads((EV/"n21-B12-lens-area.json").read_text())
    assert area["verified"] and area["global_optimality_proved"] is False and F(area["area_contradiction_margin"])>0
    count=0
    for name,expected in (("n21-peeling-round4-B12",{12:133450}),
                         ("n21-peeling-round5-B13-B14",{13:583857,14:745290})):
        folder=EV/name
        summary=json.loads((folder/"SUMMARY.json").read_text())
        assert summary["verified_small_cases"] and summary["global_optimality_proved"] is False
        assert summary["kernel_sha256"]==sha(ROOT/"peel_synthesis.cpp")
        for familyrow in summary["families"]:
            b=familyrow["B"]
            assert familyrow["complete_matching"] and b in expected
            for row in familyrow["runs"]:
                assert row["exit"]==0 and row["status"]=="complete" and row["orbits"]==expected[b]
                assert row["output_sha256"]==sha(folder/f"N21-B{b}-{row['mode']}.json")
                assert row["log_sha256"]==sha(folder/f"N21-B{b}-{row['mode']}.log")
            count+=expected[b]
    assert count==1462597
    core=json.loads((EV/"n21-positive-core-angle-tree.json.verified.json").read_text())
    maps=json.loads((EV/"n21-core-embedding-map.json").read_text())
    assert core["verified"] and core["nodes"]==4939 and core["graph_edges"]==68
    assert core["counts"]=={"SPLIT":2469,"DUAL":2312,"LOCAL":158}
    assert core["tree_sha256"]==sha(EV/"n21-positive-core-angle-tree.json.gz")
    assert maps["verified"] and maps["proved_same_core_types"]==30 and maps["remaining_B13_types_without_this_core"]==583827
    assert maps["core_angle_proof_sha256"]==sha(EV/"n21-positive-core-angle-tree.json.verified.json")
    fresh=json.loads((EV/"fresh-milestone-replay-20261003/SUMMARY.json").read_text())
    assert fresh["verified_replay_of_achieved_milestones"] and fresh["global_optimality_proved_for_any_new_n"] is False
    regression=json.loads((EV/"extended-unpruned-regressions/SUMMARY.json").read_text())
    assert regression["verified_small_cases"] and any(x["B"]==3 and x["I"]==9 for x in regression["tests"])
    return count


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--create",action="store_true")
    args=parser.parse_args()
    count=validate()
    if args.create:
        assert not SNAPSHOT.exists(),"Do not overwrite immutable joint research snapshot"
        files={p for p in ROOT.iterdir() if p.is_file() and p.suffix in (".py",".cpp",".md")}
        for foldername in ("n22","n23","n24","n25","n25-algebraic-upper-round2",
                           "n25-core-analysis-stable3","core-reduction","n21-peeling-round4-B12",
                           "n21-peeling-round5-B13-B14","extended-unpruned-regressions",
                           "fresh-milestone-replay-20261003"):
            files|={p for p in (EV/foldername).rglob("*") if p.is_file()}
        files|={EV/name for name in ("n21-B12-lens-area.json","n21-positive-core-angle-tree.json.gz",
                 "n21-positive-core-angle-tree.json.verified.json","n21-core-embedding-map.json",
                 "symbolic-family-identities.json")}
        for n in (22,23,24,25):
            files.add(ROOT.parent/f"n{n}-global/STATUS.md")
        n21=ROOT.parent/"n21-global"
        files|={n21/p for p in ("candidate_tree.py","root_certificate.py","noncandidate_probe.py",
                 "evidence/core-system.json","evidence/core-root.json",
                 "evidence/local-isolation-certificate.json","evidence/angle-constants.json",
                 "evidence/six-core-exclusion/REPLAY.json","SIX-CORE-EXCLUSION.md")}
        files.add(ROOT.parent/"n13-global/independent_checks.py")
        external=ROOT.parent/"disk-cover-proof-library/external/pinned/cover20/proof_bundle"
        files|={external/p for p in ("core/exact_arcs.py","core/compact_force20.py","discovery/force20.py")}
        record={"schema":"five-target-research-milestones-not-global-proof-v1","date":"2026-10-03",
                "timezone":"Asia/Shanghai","goal_status":"active","targets":[25,21,22,23,24],
                "global_optimality_completed":[],"complete_n21_necessary_catalog_orbits":count,
                "n21_actual_cover_remaining_boundary_counts":[13,14],
                "n21_same_core_types_paid":30,"n21_remaining_noncore_types":1329117,
                "unresolved_obligations":["n21 exclude all remaining actual B13/B14 competing types",
                    "n22/n23/n24/n25 unrestricted global lower bounds; candidate/global interfaces"],
                "external_peer_review_completed":False,"formalization_completed":False,
                "files":{p.relative_to(WORKSPACE).as_posix():sha(p) for p in sorted(files)}}
        SNAPSHOT.write_text(json.dumps(record,indent=2),encoding="utf8")
    record=json.loads(SNAPSHOT.read_text())
    assert record["goal_status"]=="active" and not record["global_optimality_completed"]
    for name,expected in record["files"].items():
        assert sha(WORKSPACE/name)==expected,("research milestone changed",name)
    print(json.dumps({"verified_integrity":True,"bound_files":len(record["files"]),
                      "all_five_global_targets_complete":False,"goal_status":"active",
                      "snapshot_sha256":sha(SNAPSHOT)},indent=2),flush=True)


if __name__=="__main__":
    main()
