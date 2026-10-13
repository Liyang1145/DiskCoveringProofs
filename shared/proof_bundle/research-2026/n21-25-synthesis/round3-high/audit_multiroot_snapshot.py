"""Independent complete-byte audit of streamed multi-root snapshots."""
from pathlib import Path, PurePosixPath
from hashlib import sha256
import argparse
import json
import time

assert __debug__


def digest(path):
    result = sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            result.update(block)
    return result.hexdigest()


def unique(pairs):
    result = {}
    for key, value in pairs:
        assert key not in result
        result[key] = value
    return result


def records(stream):
    assert stream.readline().strip() == "{"
    assert stream.readline().strip() == '"files": {'
    seen = set()
    comma = None
    while True:
        line = stream.readline()
        assert line, "truncated files object"
        text = line.strip()
        if text == "},":
            assert comma is None or not comma
            return
        assert comma is None or comma, "missing separator"
        comma = text.endswith(",")
        if comma:
            text = text[:-1]
        row = json.loads("{"+text+"}", object_pairs_hook=unique)
        assert len(row) == 1
        key, expected = next(iter(row.items()))
        assert key not in seen
        seen.add(key)
        assert type(expected) is str and len(expected) == 64
        assert all(ch in "0123456789abcdef" for ch in expected)
        p = PurePosixPath(key)
        assert not p.is_absolute() and ".." not in p.parts and len(p.parts) >= 2
        assert "\\" not in key and ":" not in key and p.as_posix() == key
        yield p.parts[0], p.parts[1:], key, expected


def audit(manifest, relocations=None):
    manifest = Path(manifest)
    before = digest(manifest)
    # Footer is parsed without retaining the hundreds of thousands of entries.
    with manifest.open(encoding="utf8") as stream:
        for _ in records(stream):
            pass
        footer = json.loads("{"+stream.read(), object_pairs_hook=unique)
    assert footer["schema"] == "disk-cover-multiroot-snapshot-v1"
    roots = {name: Path(path).resolve() for name, path in footer["roots"].items()}
    for name, path in (relocations or {}).items():
        assert name in roots
        roots[name] = Path(path).resolve()
    assert roots and all(path.is_dir() for path in roots.values())
    failures, parents = [], {}
    count = 0
    started = time.monotonic()
    with manifest.open(encoding="utf8") as stream:
        for name, parts, key, expected in records(stream):
            assert name in roots
            parentkey = (name, parts[:-1])
            if parentkey not in parents:
                parents[parentkey] = roots[name].joinpath(*parts[:-1]).resolve()
            path = parents[parentkey] / parts[-1]
            assert path.is_relative_to(roots[name]) and not path.is_symlink()
            if not path.is_file():
                failures.append({"path": key, "problem": "missing"})
            elif digest(path) != expected:
                failures.append({"path": key, "problem": "content mismatch"})
            count += 1
            if count % 10000 == 0:
                print("Multi-root snapshot all-file integrity checked", count,
                      "differences", len(failures), flush=True)
    assert count == footer["file_count"]
    assert before == digest(manifest), "manifest changed during integrity audit"
    return {"verified": not failures, "manifest_sha256": before, "file_count": count,
            "all_bound_files_checked": True, "mismatches": failures,
            "roots_used": {name: str(path) for name, path in roots.items()},
            "source_sha256": digest(Path(__file__)),
            "seconds": time.monotonic()-started,
            "scope": "all-file frozen-input byte integrity only; not mathematical proof"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--root", nargs=2, action="append")
    args = ap.parse_args()
    assert not args.output.exists()
    relocations = dict(args.root or [])
    assert len(relocations) == len(args.root or [])
    result = audit(args.manifest, relocations)
    with args.output.open("x", encoding="utf8") as stream:
        json.dump(result, stream, indent=2)
    print("Multi-root snapshot integrity", "PASS" if result["verified"] else "FAIL",
          result["file_count"], "files", flush=True)


if __name__ == "__main__":
    main()
