"""Explicit isolated root remapping and hash inventory of historical launch bytes.

No missing file is fabricated or accepted. This inventory diagnoses which
frozen source/library/control assets still need exact archive materialization.
It does not run a search or certify a mathematical pruning theorem.
"""
from pathlib import Path, PureWindowsPath
from collections import Counter
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish

assert __debug__
WORK = ROOT.parents[2]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--assets", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assets, output = args.assets.resolve(), args.output.resolve()
    assert assets.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    recoverypath = assets / "VERIFIED.json"
    recovered = read(recoverypath)
    assert recovered["verified"] and recovered["schema"] == "isolated-N23-B14-all-original-union-asset-byte-recovery-v1"
    bindingpath = assets / "SOURCE/INPUT-BINDINGS.json"
    bindings = read(bindingpath)
    assert (bindings["N"], bindings["B"], bindings["variant"]) == (23, 14, "pair")
    assert len(bindings["files_absolute"]) == 8726
    firstpath = PureWindowsPath(next(iter(bindings["files_absolute"])))
    assert firstpath.is_absolute() and firstpath.parts[:2] == ("C:\\", "Users")
    assert firstpath.parts[3:5] == ("Desktop", "ai4math2")
    # The historic username contains exact replacement/legacy Unicode bytes;
    # never retype a visually similar root. Record its exact bound spelling.
    old_work = PureWindowsPath(*firstpath.parts[:5])
    entries, counts = [], Counter()
    destinations = set()
    before = sha(bindingpath)
    for old, digest in bindings["files_absolute"].items():
        source = PureWindowsPath(old)
        assert source.is_absolute() and source.is_relative_to(old_work), ("unmapped historical root", old)
        relative = source.relative_to(old_work)
        assert ".." not in relative.parts and relative.parts
        target = (WORK / Path(*relative.parts)).resolve()
        assert target.is_relative_to(WORK) and target not in destinations
        destinations.add(target)
        if not target.is_file():
            status, actual = "missing", None
        else:
            actual = sha(target)
            status = "original-byte-sha256-matches" if actual == digest else "different-bytes-do-not-accept"
        counts[status] += 1
        entries.append({
            "old_absolute_path": old, "workspace_relative_path": relative.as_posix(),
            "mapped_absolute_path": str(target), "expected_sha256": digest,
            "observed_sha256": actual, "status": status,
        })
        if len(entries) % 1000 == 0:
            print("Historical B14 launch dependency bytes inspected:", len(entries), "/8726", dict(counts), flush=True)
    assert sha(bindingpath) == before
    output.mkdir()
    publish(output / "OBSERVATION.json", {
        "schema": "historical-N23-B14-explicit-root-launch-byte-inventory-v1",
        "N": 23, "B": 14, "historical_source_root": str(old_work),
        "mapped_current_workspace": str(WORK), "entries": entries, "counts": dict(counts),
        "all_8726_old_dependency_names_accounted_for_once": True,
        "binding_sha256": before, "recovery_report_sha256": sha(recoverypath),
        "no_missing_or_changed_dependency_accepted": True,
        "not_a_native_exhaustion_completeness_or_pruning_math_gate": True,
        "no_existing_bytes_or_live_process_modified": True,
        "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
    })
    print("Historical B14 dependency byte inventory finished:", dict(counts),
          "not a mathematical/source completeness acceptance", flush=True)


if __name__ == "__main__":
    main()
