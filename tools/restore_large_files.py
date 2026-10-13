"""Restore compressed files into a new root; refuse differing existing bytes."""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil

from bundle_io import PartsReader, safe_asset_path, sha256_file

parser = argparse.ArgumentParser()
parser.add_argument("--destination", required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
destination = Path(args.destination).resolve()
if destination == root or root in destination.parents:
    raise SystemExit("Use a destination outside the repository so restored large files are not committed.")
count = 0
for line in (root / "manifests" / "FILES.jsonl").read_text(encoding="utf-8").splitlines():
    entry = json.loads(line)
    if entry["encoding"] != "gzip-parts-v1":
        continue
    target = safe_asset_path(destination, entry["path"])
    if target.exists():
        if target.is_file() and sha256_file(target) == entry["sha256"]:
            continue
        raise SystemExit(f"Refusing to overwrite existing differing content: {target}")
    target.parent.mkdir(parents=True, exist_ok=True)
    partial = target.with_name(target.name + ".restoring")
    if partial.exists():
        raise SystemExit(f"Existing partial output preserved: {partial}")
    paths = []
    for part in entry["parts"]:
        path = safe_asset_path(root, part["path"])
        if sha256_file(path) != part["sha256"]:
            raise SystemExit(f"Corrupt part: {path}")
        paths.append(path)
    with io.BufferedReader(PartsReader(paths)) as parts, gzip.GzipFile(fileobj=parts) as source, partial.open("xb") as output:
        shutil.copyfileobj(source, output, 1024 * 1024)
    if partial.stat().st_size != entry["bytes"] or sha256_file(partial) != entry["sha256"]:
        raise SystemExit(f"Restoration failed; partial preserved: {partial}")
    partial.rename(target)
    count += 1
print(f"Restored {count} original large files into {destination}.")
