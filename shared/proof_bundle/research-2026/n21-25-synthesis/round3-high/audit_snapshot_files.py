"""Read-only full hash audit of immutable manifests; never rewrites inputs.

Hash integrity is not mathematical validity. This checks every bound file,
including scripts, and writes a new audit report even when mismatches exist.
"""
from pathlib import Path
import argparse
import json
import time
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parents[2]
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    data = json.loads(args.manifest.read_text(encoding="utf8"),
                      object_pairs_hook=no_duplicate_keys)
    bound = data["files"]
    failures = []
    started = time.monotonic()
    for index, (relative, expected) in enumerate(bound.items()):
        path = (WORK / relative).resolve()
        assert path.is_relative_to(WORK.resolve())
        if not path.is_file():
            failures.append({"path": relative, "problem": "missing"})
        else:
            actual = sha(path)
            if actual != expected:
                failures.append({"path": relative, "expected": expected, "actual": actual})
        if (index+1) % 10000 == 0:
            print("Snapshot hashes checked", index+1, "failures", len(failures),
                  "seconds", round(time.monotonic()-started, 1), flush=True)
    report = {"verified": not failures, "manifest_sha256": sha(args.manifest),
              "file_count": len(bound), "all_bound_files_checked": True,
              "mismatches": failures, "source_sha256": sha(Path(__file__)),
              "scope": "full frozen-input hash integrity only; not math proof"}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Snapshot full integrity", "PASS" if not failures else "FAIL",
          len(bound), "files;", len(failures), "mismatches", flush=True)


if __name__ == "__main__":
    main()
