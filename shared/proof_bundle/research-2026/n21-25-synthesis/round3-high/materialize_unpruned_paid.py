"""Lossless original-schema view ONLY when zero proof branches were pruned.

Nonzero payment residuals must never be promoted to full necessary catalogues.
Writes new output, then checks every row against the independent binary view.
"""
from pathlib import Path
import argparse
import json
import os
from paid_binary_residual import BinaryRows
from stream_catalog import Catalog, sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parents[2].resolve()
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", type=Path, required=True)
    ap.add_argument("--summary", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    temporary = args.output.with_suffix(".building")
    assert not temporary.exists()
    summary = json.loads(args.summary.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)
    assert summary["verified"] and summary["complete_residual_family_search"]
    assert summary["all_sorted_run_union_equality_verified"]
    assert summary["pruned_recursive_states_not_orbit_count"] == 0
    assert summary["catalog_sha256"] == sha(args.input)
    for relative, digest in summary["files"].items():
        assert sha(WORK / relative) == digest
    native = BinaryRows(args.input)
    header = native.header
    assert header["proof_prunes"] == 0 and not header["proof_payments"]
    assert header["orbits"] == summary["residual_orbits"]
    converted = {key: header[key] for key in
                 ("N", "B", "mode", "scale", "caps", "screen", "root_degree_prune",
                  "calls", "prunes", "rooted", "orbits")}
    converted["complete"] = True
    converted["paid_branches_removed"] = 0
    converted["lossless_binary_view_sha256"] = sha(args.input)
    converted["completion_receipt_sha256"] = sha(args.summary)
    with temporary.open("x", encoding="utf8") as stream:
        stream.write(json.dumps(converted, separators=(",", ":"))[:-1]+',"survivors":[')
        for index, row in native.rows():
            if index:
                stream.write(",")
            stream.write(json.dumps(row, separators=(",", ":")))
        stream.write("]}\n")
        stream.flush()
        os.fsync(stream.fileno())
    view = Catalog(temporary)
    independent = BinaryRows(args.input)
    for (i, actual), (j, expected) in zip(view.rows(), independent.rows(), strict=True):
        assert i == j and actual == expected
    assert view.finished and independent.finished
    temporary.rename(args.output)
    report = {"verified": True, "N": header["N"], "B": header["B"],
              "complete_necessary_catalogue_view": True, "paid_branches_removed": 0,
              "orbits": header["orbits"], "all_rows_losslessly_compared": True,
              "input_sha256": sha(args.input), "summary_sha256": sha(args.summary),
              "output_sha256": sha(args.output), "source_sha256": sha(Path(__file__)),
              "global_optimality_proved": False,
              "scope": "full necessary-catalogue view because native proof pruning count is zero"}
    outreport = args.output.with_suffix(".view-audit.json")
    assert not outreport.exists()
    outreport.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Full necessary-catalogue lossless view PASS:", header["orbits"],
          "types; zero proof-pruned branches; no optimum claim", flush=True)


if __name__ == "__main__":
    main()
