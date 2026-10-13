"""Diagnose every bound digest without stopping at the first mismatch.

This is a byte-integrity diagnostic, not a mathematical acceptance. Historical
targets are never modified. Mismatched bytes are copied to fresh snapshot files.
"""

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys


def local_path(text):
    text = str(text).replace("\\", "/")
    if sys.platform == "win32" and text.startswith("/mnt/"):
        return Path(text[5].upper() + ":" + text[6:])
    if sys.platform != "win32" and len(text) > 2 and text[1] == ":":
        return Path("/mnt/" + text[0].lower() + text[2:])
    return Path(text)


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def inspect(item):
    text, expected = item
    path = local_path(text)
    result = {"path": text, "expected_sha256": expected}
    try:
        before = path.stat()
        actual = sha(path)
        after = path.stat()
        stable = (before.st_size, before.st_mtime_ns) == (
            after.st_size, after.st_mtime_ns
        )
        if actual == expected and stable:
            return None
        result.update(
            actual_sha256=actual,
            size=after.st_size,
            mtime_ns=after.st_mtime_ns,
            stable_during_hash=stable,
            status="mismatch" if stable else "changed_during_hash",
        )
    except Exception as error:
        result.update(status="read_error", error=repr(error))
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--current-audit", type=Path, required=True)
    parser.add_argument("--expected-audit-sha256", required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--snapshot-dir", type=Path, required=True)
    parser.add_argument("--workers", type=int, default=8)
    args = parser.parse_args()
    if args.report.exists() or args.snapshot_dir.exists():
        raise FileExistsError("diagnosis needs a fresh report and snapshot directory")
    initial = sha(args.current_audit)
    if initial != args.expected_audit_sha256:
        raise ValueError("the expected current audit itself changed")
    current = json.loads(args.current_audit.read_text(encoding="utf-8"))
    inventory = current["files"]
    normalized = [str(local_path(text).resolve()) for text in inventory]
    if len(set(normalized)) != len(inventory):
        raise ValueError("duplicate normalized inventory paths")
    failures = []
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        for number, failure in enumerate(pool.map(inspect, inventory.items()), 1):
            if failure is not None:
                failures.append(failure)
                print(json.dumps({"failed_digest": failure}), flush=True)
            if number % 10000 == 0:
                print(json.dumps({"digests_scanned": number, "total": len(inventory)}), flush=True)
    args.snapshot_dir.mkdir(parents=True)
    for index, failure in enumerate(failures):
        if "actual_sha256" not in failure:
            continue
        path = local_path(failure["path"])
        target = args.snapshot_dir / f"{index:05d}-{path.name}.bin"
        try:
            with path.open("rb") as source, target.open("xb") as output:
                for block in iter(lambda: source.read(1024 * 1024), b""):
                    output.write(block)
            saved_sha = sha(target)
            failure.update(
                snapshot_file=str(target.resolve()),
                snapshot_sha256=saved_sha,
                snapshot_matches_observed_bytes=saved_sha == failure["actual_sha256"],
            )
        except Exception as error:
            failure["snapshot_error"] = repr(error)
    final = sha(args.current_audit)
    report = {
        "schema": "N26-complete-current-byte-integrity-diagnosis-v1",
        "observed_at_utc": datetime.now(timezone.utc).isoformat(),
        "current_audit": str(args.current_audit.resolve()),
        "current_audit_sha256": initial,
        "current_audit_unchanged": final == initial,
        "expected_digest_count": len(inventory),
        "matched_digest_count": len(inventory) - len(failures),
        "failure_count": len(failures),
        "failures_by_status": dict(Counter(row["status"] for row in failures)),
        "failures": failures,
        "all_current_bytes_match": not failures and final == initial,
        "historical_targets_modified": False,
        "mathematical_acceptance_issued": False,
        "new_geometric_payments": 0,
        "executed_diagnostic_sha256": sha(Path(__file__)),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items() if key != "failures"}, indent=2), flush=True)
    if failures or final != initial:
        sys.exit(1)


if __name__ == "__main__":
    main()
