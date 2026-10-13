"""Fresh positive slab replay and bad all-row partition rejection controls."""
from pathlib import Path
from copy import deepcopy
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from closed_origin_slab import ledger_header
import json

assert __debug__


def run(proposal_path, exact_path, terminal_path):
    process = subprocess.run([
        sys.executable, str(ROOT / "replay_closed_origin_slab.py"),
        "--proposal", str(proposal_path), "--output", str(exact_path),
    ], capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
    publish(terminal_path, {
        "actual_exit_code": process.returncode,
        "stdout": process.stdout.decode(errors="replace"), "stderr": process.stderr.decode(errors="replace"),
    })
    return process.returncode


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--payments", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    args.payments, args.output = args.payments.resolve(), args.output.resolve()
    assert args.payments.is_relative_to(ROOT) and args.output.is_relative_to(ROOT)
    assert not args.output.exists()
    source_proposal, source_exact = args.payments / "PROPOSAL.json", args.payments / "VERIFIED.json"
    proposal, accepted = read(source_proposal), read(source_exact)
    assert accepted["verified"] and accepted["schema"] == "independent-finite-origin-slab-sparse-partition-v1"
    assert accepted["proposal_sha256"] == sha(source_proposal)
    unchanged(accepted["files_relative_to_workspace"])
    args.output.mkdir()
    positive_path = args.output / "POSITIVE-EXACT.json"
    assert run(source_proposal, positive_path, args.output / "POSITIVE-TERMINAL.json") == 0
    positive = read(positive_path)
    assert positive["strictly_paid_rows"] == accepted["strictly_paid_rows"]
    assert positive["pending_rows"] == accepted["pending_rows"]
    ledger_path = args.payments / "PARTITION.jsonl"
    with ledger_path.open(encoding="ascii") as stream:
        header = json.loads(next(stream))
        first_rows = [json.loads(next(stream)) for _ in range(64)]
    assert header == ledger_header(proposal["N"], proposal["B"], proposal["slab_index"])
    assert all(row["status"] == "strict-sparse-injection" for row in first_rows)
    rejected = []
    for label in ("missing-first-row", "duplicated-first-row", "wrong-row-index",
                  "changed-source-face", "wrong-anchor-offset", "center-collision",
                  "fabricated-obstacle-id", "truncated-after-64-valid-rows"):
        directory = args.output / label
        directory.mkdir()
        bad_rows = deepcopy(first_rows)
        if label == "missing-first-row":
            bad_rows.pop(0)
        elif label == "duplicated-first-row":
            bad_rows.insert(1, deepcopy(bad_rows[0]))
        elif label == "wrong-row-index":
            bad_rows[0]["slab_row"] += 1
        elif label == "changed-source-face":
            bad_rows[0]["faces"].pop()
        elif label == "wrong-anchor-offset":
            bad_rows[0]["map"]["anchors"][0] = (bad_rows[0]["map"]["anchors"][0]+1) % proposal["B"]
        elif label == "center-collision":
            bad_rows[0]["map"]["centers"][1] = bad_rows[0]["map"]["centers"][0]
        elif label == "fabricated-obstacle-id":
            bad_rows[0]["obstacle"] = 1000000
        bad_ledger, bad_pending = directory / "PARTITION.jsonl", directory / "PENDING.jsonl"
        with bad_ledger.open("x", encoding="ascii") as stream:
            stream.write(json.dumps(header, separators=(",", ":"))+"\n")
            for row in bad_rows:
                stream.write(json.dumps(row, separators=(",", ":"))+"\n")
        with bad_pending.open("x", encoding="ascii") as stream:
            stream.write(json.dumps(header, separators=(",", ":"))+"\n")
        bad = deepcopy(proposal)
        # Rebind the deliberately changed test files: rejection must arise from
        # row coverage or the actual injection, not just a stale file hash.
        bad["partition_sha256"], bad["pending_sha256"] = sha(bad_ledger), sha(bad_pending)
        bad_proposal, bad_exact = directory / "PROPOSAL.json", directory / "EXACT.json"
        publish(bad_proposal, bad)
        assert run(bad_proposal, bad_exact, directory / "TERMINAL.json") != 0
        assert not bad_exact.exists()
        rejected.append(label)
    files = dict(accepted["files_relative_to_workspace"])
    for path in (Path(__file__), source_proposal, source_exact, ledger_path,
                 ROOT / "replay_closed_origin_slab.py", positive_path):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(args.output / "VERIFIED.json", {
        "verified": True, "schema": "finite-closed-slab-partition-rejection-controls-v1",
        "fresh_positive_all_rows_exact_replay_passed": True,
        "negative_controls_rejected": rejected,
        "changed_test_file_hashes_rebound_before_structural_rejection": True,
        "positive_source_slab_sha256": positive["source_slab_sha256"],
        "positive_exact_sha256": sha(positive_path), "source_sha256": sha(Path(__file__)),
        "files_relative_to_workspace": files,
        "not_a_complete_competitor_family_or_union": True, "global_optimality_proved": False,
    })
    print("Closed-slab partition controls PASS: one fresh all-row replay;",
          len(rejected), "structural/map rejections", flush=True)


if __name__ == "__main__":
    main()
