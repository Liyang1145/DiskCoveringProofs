"""Fail closed on credential-shaped material; print paths, never matching bytes."""
from pathlib import Path
import gzip
import io
import json
import re
from bundle_io import PartsReader, safe_asset_path

root = Path(__file__).resolve().parents[1]
patterns = [
    re.compile(rb"gh[pousr]_[A-Za-z0-9]{30,}"),
    re.compile(rb"github_pat_[A-Za-z0-9_]{40,}"),
    re.compile(rb"(?<![A-Za-z0-9_-])sk-(?:proj-)?[A-Za-z0-9_-]{40,}"),
    re.compile(rb"AKIA[0-9A-Z]{16}"),
    re.compile(rb"-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----"),
]
checked = 0


def check_stream(source, label):
    carry = b""
    for block in iter(lambda: source.read(1024 * 1024), b""):
        joined = carry + block
        if any(pattern.search(joined) for pattern in patterns):
            raise SystemExit("SENSITIVE CONTENT BLOCKED: " + label)
        carry = joined[-512:]


for path in root.rglob("*"):
    if not path.is_file() or {".git", "publication-local"}.intersection(path.relative_to(root).parts):
        continue
    if ".gz.part" in path.name or path.name.endswith(".gz"):
        # Original multipart bytes are checked through the bound manifest below.
        continue
    with path.open("rb") as source:
        check_stream(source, path.relative_to(root).as_posix())
    checked += 1
compressed_checked = 0
manifest = root / "manifests" / "FILES.jsonl"
if manifest.is_file():
    for line in manifest.read_text(encoding="utf-8").splitlines():
        entry = json.loads(line)
        if entry["encoding"] != "gzip-parts-v1":
            continue
        paths = [safe_asset_path(root, part["path"]) for part in entry["parts"]]
        with io.BufferedReader(PartsReader(paths)) as parts, gzip.GzipFile(fileobj=parts) as source:
            check_stream(source, entry["path"])
        compressed_checked += 1
print(f"CREDENTIAL-SHAPE SCAN PASSED: {checked} plain and {compressed_checked} reconstructed files.")
print("Automated scanning is not a guarantee against every possible secret format.")
