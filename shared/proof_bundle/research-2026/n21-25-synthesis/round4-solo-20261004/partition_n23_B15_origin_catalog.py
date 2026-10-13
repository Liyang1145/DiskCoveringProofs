"""Full original-byte N23/B15 catalog proposal, then a separate accepting process."""
from pathlib import Path
from collections import Counter
import argparse
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import Catalog, sha
from n25_outer_search import publish
from refine_collar_origin import exposed_mask
from audit_n23_B15_origin_catalog import N, B, TOTAL, CATALOG_SHA, UPPER, input_gate, ledger_header

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    dataset, output = args.dataset.resolve(), args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    catalogpath, gap, frozen = input_gate(dataset)
    for path in (Path(__file__).resolve(), ROOT / "refine_collar_origin.py",
                 ROOT / "audit_n23_B15_origin_catalog.py"):
        frozen[str(path)] = sha(path)
    output.mkdir()
    publish(output / "INPUT-BINDINGS.json", {
        "N": N, "B": B, "frozen_files": frozen,
        "one_shot_full_catalog_scan_not_group_member_arithmetic": True,
        "global_optimality_proved": False,
    })
    obstructions, pendingpath = output / "ORIGIN-OBSTRUCTIONS.jsonl", output / "PENDING.jsonl"
    catalog = Catalog(catalogpath)
    paid = pending = seen = 0
    counts = Counter()
    started = time.monotonic()
    with obstructions.open("x", encoding="ascii") as payments, pendingpath.open("x", encoding="ascii") as residual:
        for stream, kind in ((payments, "actual-cover-origin-obstruction"),
                             (residual, "not-paid-by-origin-condition")):
            stream.write(json.dumps(ledger_header(kind, CATALOG_SHA), separators=(",", ":"))+"\n")
        for index, row in catalog.rows():
            assert index == seen
            mask = exposed_mask(N, B, row["faces"])
            is_obstruction = mask == (1 << N)-1
            stream = payments if is_obstruction else residual
            stream.write(json.dumps({"index": index, "exposed_mask": mask}, separators=(",", ":"))+"\n")
            paid += is_obstruction
            pending += not is_obstruction
            counts[mask.bit_count()] += 1
            seen += 1
            if seen % 250000 == 0:
                print("N23/B15 origin proposals", seen, "obstructions", paid,
                      "pending", pending, "seconds", round(time.monotonic()-started, 2), flush=True)
    assert catalog.finished and seen == TOTAL == paid+pending
    for path, digest in frozen.items():
        assert sha(path) == digest
    proposalpath = output / "PROPOSAL.json"
    publish(proposalpath, {
        "schema": "proposal-frozen-N23-B15-full-type-origin-partition-v1",
        "N": N, "B": B, "catalog_types": TOTAL,
        "actual_cover_origin_obstructions": paid, "pending_full_types": pending,
        "exposed_center_histogram": dict(sorted(counts.items())),
        "radius_upper": str(UPPER), "strict_gap_1_minus_4U": str(gap),
        "catalog_sha256": CATALOG_SHA,
        "origin_obstructions_sha256": sha(obstructions), "pending_sha256": sha(pendingpath),
        "frozen_files": frozen, "source_sha256": sha(Path(__file__)),
        "not_independently_accepted_until_separate_fresh_full_scan": True,
        "global_optimality_proved": False,
    })
    script = ROOT / "audit_n23_B15_origin_catalog.py"
    with (output / "AUDIT-STDOUT.log").open("xb") as stdout, (output / "AUDIT-STDERR.log").open("xb") as stderr:
        process = subprocess.Popen([
            sys.executable, "-u", str(script), "--dataset", str(dataset),
            "--proposal", str(proposalpath), "--output", str(output / "ACCEPTED")],
            cwd=str(ROOT), stdout=stdout, stderr=stderr,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        code = process.wait()
    publish(output / "AUDIT-TERMINAL.json", {
        "actual_exit_code": code, "child_pid": process.pid,
        "source_sha256": sha(script), "exit_zero_is_not_a_global_proof": True,
    })
    assert code == 0, ("independent full-row accepting process failed", code)
    print("N23/B15 proposal and independent whole-catalog origin audit ended", flush=True)


if __name__ == "__main__":
    main()
