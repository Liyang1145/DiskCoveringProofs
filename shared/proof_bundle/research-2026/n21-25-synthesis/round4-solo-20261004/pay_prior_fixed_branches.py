"""Reprove the seven non-V25 legacy closure parents by exact complete branch covers."""
from pathlib import Path
import argparse
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from n25_outer_search import read, publish, unchanged
from stream_catalog import sha, no_duplicate_keys
from prove_paid_hole import propose

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    controls = read(ROOT / "n25-paid-hole-controls-20261005-v1/VERIFIED.json")
    assert controls["verified"] and controls["kernel_sha256"] == sha(ROOT / "proof_paid_hole_kernel.py")
    assert controls["source_induction_sha256"] == sha(ROOT / "PROOF-PAID-HOLE-SOURCE.md")
    unchanged(controls["files_relative_to_workspace"])
    groupspath = ROOT / "n25-B14-sparse-collar-search-resume-20261005-v1/GROUPS.json"
    data = read(groupspath)
    selected = set()
    for name in ("n25-B14-complete-old-collar-paid-partition-20261005-v2",
                 "n25-B14-origin-force-refined-residual-20261005-v1"):
        directory = ROOT / name
        report = read(directory / "VERIFIED.json")
        assert report["verified"] and sha(directory / "PAYMENTS.jsonl") == report["payments_sha256"]
        with (directory / "PAYMENTS.jsonl").open(encoding="ascii") as stream:
            for line in stream:
                row = json.loads(line, object_pairs_hook=no_duplicate_keys)
                if "completion-family" in row["kind"] and data["groups"][row["parent_group"]]["centers"] < 25:
                    selected.add(row["parent_group"])
    assert len(selected) == 7
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    output.mkdir()
    results = []
    for gid in sorted(selected):
        row = data["groups"][gid]
        directory = output / f"parent-{gid:07}";directory.mkdir()
        collarpath, proposalpath, exactpath = (directory / name for name in
                                              ("INPUT-COLLAR.json", "PROPOSAL.json", "EXACT.json"))
        collar = {"N": 25, "B": 14, "centers": row["centers"], "faces": row["faces"], "source_parent_group": gid}
        publish(collarpath, collar)
        payload = propose(collar, constants, 20000, 1)
        payload.update(source_collar_sha256=sha(collarpath), constants_sha256=sha(constants_path),
                       kernel_sha256=sha(ROOT / "proof_paid_hole_kernel.py"),
                       source_sha256=sha(ROOT / "prove_paid_hole.py"), global_optimality_proved=False)
        publish(proposalpath, payload)
        process = subprocess.run([
            sys.executable, str(ROOT / "replay_paid_hole.py"), "--collar", str(collarpath),
            "--proposal", str(proposalpath), "--output", str(exactpath),
        ], capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        publish(directory / "REPLAY-TERMINAL.json", {
            "actual_exit_code": process.returncode, "independent_process_terminal_observed": True,
            "stdout": process.stdout.decode(errors="replace"), "stderr": process.stderr.decode(errors="replace"),
        })
        assert process.returncode == 0, (process.stdout, process.stderr)
        accepted = read(exactpath)
        assert accepted["verified"] and accepted["all_full_simple_disk_completions_strictly_paid"]
        status = {"parent_group": gid, "fully_paid": True, "exact_sha256": sha(exactpath),
                  "proposal_sha256": sha(proposalpath), "branch_nodes": accepted["nodes"]}
        publish(directory / "STATUS.json", status)
        results.append(status)
        print("Prior fixed family fresh branch payment:", gid, accepted["nodes"], "nodes", flush=True)
    publish(output / "SUMMARY.json", {
        "verified": True, "N": 25, "B": 14, "selected_parent_groups": sorted(selected),
        "all_selected_complete_simple_hole_families_strictly_paid": True, "results": results,
        "parent_catalog_sha256": sha(groupspath), "source_sha256": sha(Path(__file__)),
        "not_new_types_or_additive_payment_count": True, "global_optimality_proved": False,
    })


if __name__ == "__main__":
    main()
