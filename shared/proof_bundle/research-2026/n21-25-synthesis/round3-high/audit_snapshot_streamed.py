"""Independent low-memory full-byte audit for the freezer's streamed manifest.

Reads every file; directory resolution is cached, not file hashes. This is
integrity evidence only. This script does not import the proof freezer.
"""
from pathlib import Path, PurePosixPath
from hashlib import sha256
import argparse
import json
import time

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parents[2].resolve()
assert __debug__


def digest(path):
    result = sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            result.update(chunk)
    return result.hexdigest()


def unique(pairs):
    row = {}
    for key, value in pairs:
        assert key not in row, ("duplicate JSON key", key)
        row[key] = value
    return row


def records(stream):
    assert stream.readline().strip() == "{"
    assert stream.readline().strip() == '"files": {'
    seen = set()
    previous_comma = None
    while True:
        line = stream.readline()
        assert line, "truncated manifest"
        text = line.strip()
        if text == "},":
            assert previous_comma is None or not previous_comma, "trailing files comma"
            return
        assert text and (previous_comma is None or previous_comma), "missing files comma"
        previous_comma = text.endswith(",")
        if previous_comma:
            text = text[:-1]
        row = json.loads("{"+text+"}", object_pairs_hook=unique)
        assert len(row) == 1
        relative, expected = next(iter(row.items()))
        assert relative not in seen
        seen.add(relative)
        assert type(expected) is str and len(expected) == 64
        assert all(ch in "0123456789abcdef" for ch in expected)
        posix = PurePosixPath(relative)
        assert not posix.is_absolute() and ".." not in posix.parts
        assert "\\" not in relative and ":" not in relative
        assert relative == posix.as_posix()
        yield relative, expected


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    manifesthash = digest(args.manifest)
    parents = {}
    failures = []
    count = 0
    started = time.monotonic()
    with args.manifest.open(encoding="utf8") as stream:
        for relative, expected in records(stream):
            path = WORK / relative
            parentkey = str(path.parent)
            if parentkey not in parents:
                parents[parentkey] = path.parent.resolve()
                assert parents[parentkey].is_relative_to(WORK)
            resolved = parents[parentkey] / path.name
            assert not resolved.is_symlink()
            if not resolved.is_file():
                failures.append({"path": relative, "problem": "missing"})
            else:
                actual = digest(resolved)
                if actual != expected:
                    failures.append({"path": relative, "expected": expected, "actual": actual})
            count += 1
            if count % 10000 == 0:
                print("Independent snapshot bytes checked", count, "mismatches", len(failures),
                      "seconds", round(time.monotonic()-started, 1), flush=True)
        metadata = json.loads("{"+stream.read(), object_pairs_hook=unique)
    assert "files" not in metadata and metadata["file_count"] == count
    assert metadata["N"] == 22 and metadata["global_optimality_source_proof_completed"]
    assert digest(args.manifest) == manifesthash, "manifest changed during audit"
    report = {"verified": not failures, "manifest_sha256": manifesthash,
              "file_count": count, "all_bound_files_checked": True, "mismatches": failures,
              "source_sha256": digest(Path(__file__)),
              "seconds": time.monotonic()-started,
              "scope": "independent full frozen-input byte integrity only; not mathematical proof"}
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Independent full snapshot integrity", "PASS" if not failures else "FAIL",
          count, "files", len(failures), "mismatches", flush=True)


if __name__ == "__main__":
    main()
