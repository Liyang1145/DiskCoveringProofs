"""Partial N25 metadata diagnostic, NOT content/math/global acceptance.

Find missing/conflicting premise names in the three ended lower chains and
accepted source/core interfaces before the future B17 final exists.
"""
from pathlib import Path
from collections import deque
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parents[2]
INCOMING = ROOT.parents[4]
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import read, publish
from bind_n25_all_final_prerequisites import (
    SOURCEPATH, COREPATH, BUDGETPATH, DOCUMENT, ERRATUM, OLDROOT17, FINALPATHS)

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    queue, entries, seen = deque(), {}, set()
    missing, escaped, conflicts = [], [], []
    def add(path, digest):
        path = Path(path).resolve()
        assert type(digest) is str and len(digest) == 64
        if not (path.is_relative_to(INCOMING) or path.is_relative_to(INCOMING.parent / "dependencies")):
            escaped.append(str(path))
            return
        if path in entries:
            if entries[path] != digest:
                conflicts.append(str(path))
            return
        entries[path] = digest
        if not path.is_file():
            missing.append(str(path))
            return
        if path.suffix.lower() == ".json":
            queue.append(path)
    entrypaths = [
        SOURCEPATH, COREPATH, BUDGETPATH, DOCUMENT, ERRATUM, OLDROOT17,
        *[FINALPATHS[b] for b in (14, 15, 16)],
        ROOT.parent / "round3-high/evidence/N25-ENDPOINT-CORE-LOWER-SNAPSHOT-resume1.json"]
    for path in entrypaths:
        add(path, sha(path))
    while queue:
        path = queue.popleft()
        if path in seen:
            continue
        seen.add(path)
        record = read(path)
        if not isinstance(record, dict):
            continue
        for field in ("frozen_files", "files_relative_to_workspace", "files",
                      "frozen_actual_worker_reports_and_original_families",
                      "new_global_entry_frozen_files"):
            values = record.get(field)
            if not isinstance(values, dict):
                continue
            if field == "files" and not all(isinstance(value, str) and len(value) == 64
                                            for value in values.values()):
                continue
            for name, digest in values.items():
                target = Path(name)
                if field == "files_relative_to_workspace" or not target.is_absolute():
                    target = WORK / name
                add(target, digest)
        for name, value in record.get("archive_bindings", {}).items():
            if isinstance(value, dict) and "archive_sha256" in value:
                target = Path(name)
                if not target.is_absolute():
                    assert target.name == name
                    target = INCOMING / name
                add(target, value["archive_sha256"])
        if len(seen) % 1000 == 0:
            print("N25 AVAILABLE-ONLY dependency name diagnostic", len(seen), "JSON objects",
                  len(entries), "paths", len(missing), "missing", flush=True)
    output.mkdir()
    ledger = output / "AVAILABLE-EXPECTED-PATHS.jsonl"
    with ledger.open("x", encoding="ascii") as stream:
        for path, digest in sorted(entries.items(), key=lambda item: str(item[0])):
            stream.write(json.dumps({"path": str(path), "expected_sha256_not_rehashed": digest},
                                    separators=(",", ":"))+"\n")
    publish(output / "METADATA-DIAGNOSTIC.json", {
        "metadata_diagnostic_completed": True, "N": 25, "available_ended_lower_families_only": [14, 15, 16],
        "B17_actual_final_NOT_included_and_NOT_claimed_available": True,
        "scanned_bound_JSON_objects": len(seen), "expected_path_names": len(entries),
        "missing_required_available_scope_paths": missing, "escaped_proof_root_paths": escaped,
        "conflicting_expected_content_identities": conflicts,
        "all_contents_NOT_rehashed_and_old_mathematics_NOT_replayed": True,
        "NOT_a_current_content_acceptance_NOT_a_math_payment_NOT_a_global_proof": True,
        "partial_expected_path_ledger_sha256": sha(ledger), "source_sha256": sha(Path(__file__)),
        "global_optimality_proved": False})
    print("N25 AVAILABLE-ONLY dependency name diagnostic complete:", len(entries), "paths;",
          len(missing), "missing", len(escaped), "escaped", len(conflicts), "conflicts;",
          "not content or global acceptance", flush=True)


if __name__ == "__main__":
    main()
