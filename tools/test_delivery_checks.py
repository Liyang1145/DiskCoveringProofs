"""Small fail-closed delivery tests; never mutate any imported evidence."""
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

TOOLS = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


def run(fixture, script, success, *arguments):
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["PYTHONIOENCODING"] = "utf-8"
    result = subprocess.run(
        [sys.executable, "-O", str(fixture / "tools" / script), *arguments],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=environment,
        encoding="utf-8", check=False,
    )
    require((result.returncode == 0) == success, "Unexpected fixture result: " + script)


with tempfile.TemporaryDirectory(prefix="disk-covering-delivery-tests-") as temporary:
    area = Path(temporary)
    fixture = area / "repository"
    (fixture / "tools").mkdir(parents=True)
    (fixture / "manifests").mkdir()
    for name in ("bundle_io.py", "verify_delivery.py", "restore_large_files.py"):
        shutil.copyfile(TOOLS / name, fixture / "tools" / name)
    original = b"original exact certificate bytes\n"
    logical = fixture / "certificate.bin"
    logical.write_bytes(original)
    entry = {
        "path": "certificate.bin", "bytes": len(original),
        "sha256": hashlib.sha256(original).hexdigest(), "encoding": "identity",
    }
    manifest = fixture / "manifests" / "FILES.jsonl"
    manifest.write_text(json.dumps(entry) + "\n", encoding="utf-8")
    (fixture / "manifests" / "SUMMARY.json").write_text('{"delivered_files":1}', encoding="utf-8")
    run(fixture, "verify_delivery.py", True)
    logical.write_bytes(b"X" + original[1:])
    run(fixture, "verify_delivery.py", False)
    escape = area / "escape.bin"
    escape.write_bytes(original)
    unsafe_entry = dict(entry, path="../escape.bin")
    manifest.write_text(json.dumps(unsafe_entry) + "\n", encoding="utf-8")
    run(fixture, "verify_delivery.py", False)
    manifest.write_text(json.dumps(entry) + "\n", encoding="utf-8")
    logical.rename(fixture / "preserved-bad-fixture.bin")
    run(fixture, "verify_delivery.py", False)
    compressed = gzip.compress(original * 1000, mtime=0)
    parts = []
    for index, block in enumerate((compressed[:19], compressed[19:]), 1):
        part = fixture / f"certificate.gz.part{index:04d}"
        part.write_bytes(block)
        parts.append({
            "path": part.name, "bytes": len(block),
            "sha256": hashlib.sha256(block).hexdigest(),
        })
    entry = {
        "path": "certificate.bin", "bytes": len(original) * 1000,
        "sha256": hashlib.sha256(original * 1000).hexdigest(),
        "encoding": "gzip-parts-v1", "parts": parts,
    }
    manifest.write_text(json.dumps(entry) + "\n", encoding="utf-8")
    run(fixture, "verify_delivery.py", True)
    first = fixture / parts[0]["path"]
    first.write_bytes(b"X" + compressed[1:19])
    run(fixture, "verify_delivery.py", False)
    first.write_bytes(compressed[:19])
    original_hash = entry["sha256"]
    entry["sha256"] = "0" * 64
    manifest.write_text(json.dumps(entry) + "\n", encoding="utf-8")
    run(fixture, "verify_delivery.py", False)
    entry["sha256"] = original_hash
    manifest.write_text(json.dumps(entry) + "\n", encoding="utf-8")
    destination = area / "restored"
    run(fixture, "restore_large_files.py", True, "--destination", str(destination))
    require((destination / "certificate.bin").read_bytes() == original * 1000, "Restored bytes differ")
    (destination / "certificate.bin").write_bytes(b"must not overwrite")
    run(fixture, "restore_large_files.py", False, "--destination", str(destination))
    require((destination / "certificate.bin").read_bytes() == b"must not overwrite", "Existing bytes overwritten")
print("DELIVERY REJECTION CONTROLS PASSED: valid identity/gzip, bad bytes, missing file, path escape, bad part, bad raw hash, no overwrite.")
