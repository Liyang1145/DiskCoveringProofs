"""Verify committed bytes and gzip reconstruction, never mathematical claims."""
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys

from bundle_io import PartsReader, safe_asset_path, sha256_file

root = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


manifest = root / "manifests" / "FILES.jsonl"
if not manifest.is_file():
    sys.exit("FAIL: delivery manifest missing")
count = 0
restored_bytes = 0
known = set()
for line in manifest.read_text(encoding="utf-8").splitlines():
    entry = json.loads(line)
    if entry["path"] in known:
        sys.exit("FAIL: duplicate logical path: " + entry["path"])
    known.add(entry["path"])
    if entry["encoding"] == "identity":
        path = safe_asset_path(root, entry["path"])
        require(path.is_file(), f"Missing {entry['path']}")
        require(path.stat().st_size == entry["bytes"], f"Size mismatch {entry['path']}")
        require(sha256_file(path) == entry["sha256"], f"Digest mismatch {entry['path']}")
    elif entry["encoding"] == "gzip-parts-v1":
        paths = []
        for part in entry["parts"]:
            path = safe_asset_path(root, part["path"])
            require(path.is_file(), f"Missing part {part['path']}")
            require(path.stat().st_size == part["bytes"], f"Part size mismatch {part['path']}")
            require(sha256_file(path) == part["sha256"], f"Part digest mismatch {part['path']}")
            paths.append(path)
        digest = hashlib.sha256()
        total = 0
        with io.BufferedReader(PartsReader(paths)) as parts, gzip.GzipFile(fileobj=parts) as stream:
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(block)
                total += len(block)
        require(total == entry["bytes"], f"Restored size mismatch {entry['path']}")
        require(digest.hexdigest() == entry["sha256"], f"Restored digest mismatch {entry['path']}")
        restored_bytes += total
    else:
        sys.exit("FAIL: unknown encoding")
    count += 1
    if count % 1000 == 0:
        print(f"Delivery bytes verified: {count}", flush=True)
summary = json.loads((root / "manifests" / "SUMMARY.json").read_text(encoding="utf-8"))
require(count == summary["delivered_files"], "Summary count mismatch")
print(f"DELIVERY BYTE CHECK PASSED: {count} files; {restored_bytes} losslessly restored bytes.")
print("Not a mathematical replay or a global-optimality acceptance.")
