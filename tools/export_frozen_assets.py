# SPDX-License-Identifier: MIT
"""Export only ledger-bound bytes, never interpret acceptance flags as proofs.

Examples (all paths may contain spaces or Unicode):
  python tools/export_frozen_assets.py --ledger closure.jsonl.gz \
      --asset-root /data/integration/assets --output /data/public-export
  python tools/export_frozen_assets.py --ledger independent-controls.json \
      --root-map server-roots.json --audit-only --output /data/preflight

Root maps have the explicit form
  {"roots": [{"original": "C:\\old\\work", "local": "/data/work",
              "namespace": "work"}]}
The longest matching original root wins. ZIP entries are assets/<canonical>;
FILES.jsonl.gz records the same canonical names, raw lengths and SHA256 hashes.
Every source is audited before packaging and checked again while copying. The
temporary index permits large ledgers without loading them all into memory.
Existing output files are never overwritten. There is no network operation.
"""

import argparse
from collections import Counter
from contextlib import closing, contextmanager
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath, PureWindowsPath
import re
import sqlite3
import sys
import tempfile
import zipfile


CHUNK = 1024 * 1024
SHA256 = re.compile(r"^[0-9a-fA-F]{64}$")
RESERVED = re.compile(r"^(CON|PRN|AUX|NUL|COM[1-9]|LPT[1-9])(?:\.|$)", re.I)


class Rejected(ValueError):
    def __init__(self, code, reason):
        super().__init__(reason)
        self.code = code


def safe_relative(name):
    """Require a single portable spelling, before pathlib normalizes it."""
    if not isinstance(name, str) or not name or name.startswith("/"):
        raise Rejected("unsafe_path", "Expected a nonempty relative canonical path")
    if "\\" in name or any(ord(ch) < 32 for ch in name):
        raise Rejected("unsafe_path", "Noncanonical separator or control character")
    parts = name.split("/")
    for part in parts:
        if part in ("", ".", "..") or part[-1:] in (".", " "):
            raise Rejected("unsafe_path", "Empty, traversal or ambiguous path component")
        if any(ch in part for ch in ':*?"<>|') or RESERVED.match(part):
            raise Rejected("unsafe_path", "Path component is not portable")
    return name


def digest_file(path):
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        while block := stream.read(CHUNK):
            digest.update(block)
            size += len(block)
    return digest.hexdigest(), size


def expected_hash(value):
    if not isinstance(value, str) or not SHA256.fullmatch(value):
        raise Rejected("invalid_ledger", "Expected a 64-digit SHA256 hash")
    return value.lower()


@contextmanager
def ledger_stream(path):
    opener = gzip.open if path.suffix.lower() == ".gz" else open
    with opener(path, "rt", encoding="utf-8-sig", newline=None) as stream:
        yield stream


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise Rejected("conflict", "Duplicate JSON object key")
        result[key] = value
    return result


def load_json(text):
    try:
        return json.loads(text, object_pairs_hook=unique_object)
    except json.JSONDecodeError as exc:
        raise Rejected("invalid_ledger", "Malformed JSON") from exc


def ledger_rows(path, ledger_field=None, metadata=None):
    """Read JSONL/gzip JSONL or explicit input_sha256/files path-hash maps."""
    with ledger_stream(path) as stream:
        first = next(((n, line) for n, line in enumerate(stream, 1) if line.strip()), None)
        if first is None:
            return
        line_number, line = first
        try:
            parsed = load_json(line)
        except Rejected as exc:
            if exc.code == "conflict":
                raise
            # Pretty-printed path-hash controls are the only multi-line JSON format.
            parsed = load_json(line + stream.read())
            if not isinstance(parsed, dict) or not {"input_sha256", "files"}.intersection(parsed):
                raise Rejected("invalid_ledger", "Use JSONL entries or explicit path-hash controls")
        fields = {"input_sha256", "files"}.intersection(parsed) if isinstance(parsed, dict) else set()
        if fields or ledger_field:
            if ledger_field:
                if ledger_field not in fields:
                    raise Rejected("invalid_ledger", "Requested ledger field is missing")
                selected = ledger_field
            else:
                if len(fields) != 1:
                    raise Rejected("conflict", "Ambiguous controls fields; select ledger-field explicitly")
                selected = fields.pop()
            if metadata is not None:
                metadata["format"] = "json-path-hash-map"
                metadata["field"] = selected
            inputs = parsed[selected]
            if not isinstance(inputs, dict):
                raise Rejected("invalid_ledger", "Selected ledger field must be a path-to-hash object")
            if stream.read().strip():
                raise Rejected("invalid_ledger", "Unexpected data after controls JSON")
            for n, (path_name, sha) in enumerate(inputs.items(), 1):
                yield n, {"path": path_name, "sha256": sha}
            return
        if metadata is not None:
            metadata["format"] = "jsonl"
        yield line_number, parsed
        for n, following in enumerate(stream, line_number + 1):
            if following.strip():
                yield n, load_json(following)


def source_parts(name):
    if not isinstance(name, str) or not name or "\x00" in name:
        raise Rejected("unsafe_path", "Invalid source path")
    # Windows absolute paths are interpreted lexically even on a Unix server.
    windows = PureWindowsPath(name)
    if windows.is_absolute():
        if any(part in (".", "..") for part in re.split(r"[\\/]", name)):
            raise Rejected("unsafe_path", "Source path contains traversal")
        if name.startswith(("\\\\?\\", "\\\\.\\")):
            raise Rejected("unsafe_path", "Windows device paths are not supported")
        return "windows", tuple(part.casefold() for part in windows.parts), windows.parts
    if name.startswith("/"):
        if any(part in (".", "..") for part in name.split("/")) or "\\" in name:
            raise Rejected("unsafe_path", "Source path contains traversal or ambiguous separators")
        parts = PurePosixPath(name).parts
        return "posix", parts, parts
    raise Rejected("unmapped", "Absolute source path has no explicit root mapping")


def contained_file(root, relative):
    safe_relative(relative)
    resolved = (root / Path(*relative.split("/"))).resolve()
    if resolved == root or root not in resolved.parents:
        raise Rejected("unsafe_path", "Source escapes its explicit local root")
    return resolved


class Resolver:
    def __init__(self, asset_root=None, map_path=None):
        self.asset_root = Path(asset_root).resolve() if asset_root else None
        self.maps = []
        self.map_sha256 = None
        if self.asset_root is not None and not self.asset_root.is_dir():
            raise Rejected("unmapped", "asset-root must be an existing directory")
        if map_path:
            path = Path(map_path)
            self.map_sha256, _ = digest_file(path)
            value = load_json(path.read_text(encoding="utf-8-sig"))
            if not isinstance(value, dict) or not isinstance(value.get("roots"), list):
                raise Rejected("invalid_mapping", "Root map must contain roots[]")
            seen = set()
            for entry in value["roots"]:
                if not isinstance(entry, dict):
                    raise Rejected("invalid_mapping", "Root entry must be an object")
                kind, prefix, _ = source_parts(entry.get("original"))
                namespace = safe_relative(entry.get("namespace"))
                local_name = entry.get("local")
                if not isinstance(local_name, str) or not Path(local_name).is_absolute():
                    raise Rejected("invalid_mapping", "Local root must be an absolute local path")
                local = Path(local_name).resolve()
                if not local.is_dir():
                    raise Rejected("invalid_mapping", "Local root must be an existing directory")
                key = kind, prefix
                if key in seen:
                    raise Rejected("conflict", "Duplicate original mapping root")
                seen.add(key)
                self.maps.append((kind, prefix, namespace, local))
            self.maps.sort(key=lambda item: len(item[1]), reverse=True)
        if self.asset_root is None and not self.maps:
            raise Rejected("unmapped", "Provide asset-root or explicit original-to-local root maps")

    def resolve(self, row):
        if not isinstance(row, dict):
            raise Rejected("invalid_ledger", "Ledger entry must be an object")
        canonical = row.get("canonical")
        if canonical is not None:
            canonical = safe_relative(canonical)
            if self.asset_root is None:
                raise Rejected("unmapped", "Canonical entries require asset-root")
            return canonical, contained_file(self.asset_root, canonical)
        source = row.get("path")
        if not isinstance(source, str):
            raise Rejected("invalid_ledger", "Entry must provide canonical or path")
        if not PureWindowsPath(source).is_absolute() and not source.startswith("/"):
            canonical = safe_relative(source)
            if self.asset_root is None:
                raise Rejected("unmapped", "Relative path entries require asset-root")
            return canonical, contained_file(self.asset_root, canonical)
        kind, folded, parts = source_parts(source)
        for root_kind, prefix, namespace, local in self.maps:
            if kind == root_kind and folded[:len(prefix)] == prefix:
                tail = parts[len(prefix):]
                if not tail:
                    raise Rejected("unsafe_path", "Ledger entry names a root rather than a file")
                relative = safe_relative("/".join(tail))
                return safe_relative(namespace + "/" + relative), contained_file(local, relative)
        raise Rejected("unmapped", "Source is outside all explicit original roots")


class Audit:
    def __init__(self):
        self.errors = Counter()
        self.examples = []
        self.rows = 0
        self.duplicates = 0
        self.verified_files = 0
        self.verified_bytes = 0

    def reject(self, error, row=None, canonical=None):
        self.errors[error.code] += 1
        if len(self.examples) < 20:
            example = {"category": error.code, "reason": str(error)}
            if row is not None:
                example["row"] = row
            if canonical is not None:
                example["canonical"] = canonical
            self.examples.append(example)


def index_ledger(index, ledger, resolver, audit, ledger_field=None, metadata=None):
    index.execute("""CREATE TABLE entries (
        canonical TEXT PRIMARY KEY, folded TEXT UNIQUE, source TEXT,
        sha256 TEXT, expected_bytes INTEGER, bytes INTEGER)""")
    try:
        for n, row in ledger_rows(ledger, ledger_field, metadata):
            audit.rows += 1
            canonical = None
            try:
                canonical, source = resolver.resolve(row)
                sha = expected_hash(row.get("sha256"))
                size = row.get("bytes")
                if size is not None and (type(size) is not int or size < 0 or size > 2**63 - 1):
                    raise Rejected("invalid_ledger", "Byte length must be a nonnegative integer")
                previous = index.execute(
                    "SELECT canonical, source, sha256, expected_bytes FROM entries WHERE folded=?",
                    (canonical.casefold(),),
                ).fetchone()
                if previous:
                    if previous != (canonical, str(source), sha, size):
                        raise Rejected("conflict", "Conflicting duplicate or case-colliding canonical path")
                    audit.duplicates += 1
                    continue
                index.execute("INSERT INTO entries VALUES (?, ?, ?, ?, ?, NULL)",
                              (canonical, canonical.casefold(), str(source), sha, size))
            except Rejected as exc:
                audit.reject(exc, n, canonical)
        index.commit()
    except (Rejected, UnicodeError, OSError, EOFError) as exc:
        if not isinstance(exc, Rejected):
            exc = Rejected("invalid_ledger", "Could not decode the complete ledger")
        audit.reject(exc)
    if audit.rows == 0:
        audit.reject(Rejected("empty_ledger", "A zero-entry ledger cannot establish completeness"))


def audit_files(index, audit, budget=None):
    for canonical, source, sha, expected_size in index.execute(
            "SELECT canonical, source, sha256, expected_bytes FROM entries ORDER BY canonical"):
        try:
            path = Path(source)
            if not path.is_file():
                raise Rejected("missing", "Ledger-bound regular file is missing")
            if path.resolve() != path:
                raise Rejected("unsafe_path", "Source links changed after root containment was checked")
            # Reject before reading a huge file which cannot fit the selected budget.
            if budget is not None and path.stat().st_size > budget:
                raise Rejected("oversized", "Single file exceeds the package uncompressed-byte budget")
            actual_sha, actual_size = digest_file(path)
            if actual_sha != sha:
                raise Rejected("hash_mismatch", "File SHA256 differs from frozen ledger")
            if expected_size is not None and actual_size != expected_size:
                raise Rejected("size_mismatch", "File byte length differs from frozen ledger")
            index.execute("UPDATE entries SET bytes=? WHERE canonical=?", (actual_size, canonical))
            audit.verified_files += 1
            audit.verified_bytes += actual_size
        except (OSError, Rejected) as exc:
            if not isinstance(exc, Rejected):
                exc = Rejected("unreadable", "Ledger-bound file cannot be read")
            audit.reject(exc, canonical=canonical)
    index.commit()


def write_inventory(index, path):
    with path.open("wb") as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as compressed:
            with io.TextIOWrapper(compressed, encoding="utf-8", newline="\n") as stream:
                for canonical, sha, size in index.execute(
                        "SELECT canonical, sha256, bytes FROM entries ORDER BY canonical"):
                    stream.write(json.dumps({"canonical": canonical, "sha256": sha, "bytes": size},
                                            ensure_ascii=False, sort_keys=True) + "\n")


def make_packages(index, staging, budget):
    packages = []
    archive = None
    raw_bytes = 0
    rows = 0
    path = None

    def close_package():
        nonlocal archive
        if archive is not None:
            archive.close()
            archive = None
            sha, length = digest_file(path)
            packages.append({"file": path.name, "sha256": sha, "bytes": length,
                             "uncompressed_bytes": raw_bytes, "files": rows})

    try:
        for canonical, source, expected_sha, size in index.execute(
                "SELECT canonical, source, sha256, bytes FROM entries ORDER BY canonical"):
            if archive is None or raw_bytes + size > budget:
                close_package()
                path = staging / f"frozen-assets-{len(packages) + 1:04d}.zip"
                archive = zipfile.ZipFile(path, "x", compression=zipfile.ZIP_DEFLATED,
                                          compresslevel=6, allowZip64=True)
                raw_bytes, rows = 0, 0
            info = zipfile.ZipInfo("assets/" + canonical, date_time=(2000, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            info.create_system = 3
            digest, copied = hashlib.sha256(), 0
            if Path(source).resolve() != Path(source):
                raise Rejected("unsafe_path", "Source links changed after their complete audit")
            with Path(source).open("rb") as source_stream:
                with archive.open(info, "w", force_zip64=True) as destination:
                    while block := source_stream.read(CHUNK):
                        copied += len(block)
                        if copied > size:
                            raise Rejected("changed_during_export", "File grew after its complete audit")
                        destination.write(block)
                        digest.update(block)
            if copied != size or digest.hexdigest() != expected_sha:
                raise Rejected("changed_during_export", "File bytes changed after their complete audit")
            raw_bytes += copied
            rows += 1
        close_package()
    finally:
        if archive is not None:
            archive.close()
    return packages


def write_json(path, value):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2, sort_keys=True)
        stream.write("\n")


def positive_integer(value):
    number = int(value)
    if number < 1:
        raise argparse.ArgumentTypeError("Must be a positive integer")
    return number


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--ledger", required=True, type=Path)
    parser.add_argument("--ledger-field", choices=("input_sha256", "files"),
                        help="Select an explicit top-level path-to-SHA256 map; otherwise auto-detect one")
    parser.add_argument("--ledger-sha256", help="Pin SHA256 of the ledger file bytes (compressed bytes for gzip)")
    parser.add_argument("--asset-root", type=Path, help="Existing directory containing canonical assets")
    parser.add_argument("--root-map", type=Path, help="Explicit original/local/namespace root mapping JSON")
    parser.add_argument("--output", required=True, type=Path, help="New or empty output directory")
    parser.add_argument("--audit-only", action="store_true", help="Hash every source and export inventory, without ZIPs")
    limits = parser.add_mutually_exclusive_group()
    limits.add_argument("--max-uncompressed-mib", type=positive_integer, help="Per-package raw byte budget (default 512 MiB)")
    limits.add_argument("--max-package-bytes", type=positive_integer, help="Exact per-package raw byte budget")
    args = parser.parse_args(argv)
    output = args.output.resolve()
    if output.exists() and (not output.is_dir() or any(output.iterdir())):
        parser.error("Output must be a new or empty directory; existing files are never overwritten")
    output.mkdir(parents=True, exist_ok=True)
    audit = Audit()
    summary = {"schema": "frozen-assets-export-v1", "complete": False,
               "publishable_bundle": False, "mathematical_verification": "not_performed",
               "scope": "Only explicitly ledger-bound bytes; acceptance flags are not mathematical replay",
               "mode": "audit" if args.audit_only else "package"}
    budget = args.max_package_bytes or (args.max_uncompressed_mib or 512) * 1024 * 1024
    summary["max_package_uncompressed_bytes"] = budget
    published = []
    try:
        ledger_sha, ledger_length = digest_file(args.ledger)
        summary["ledger"] = {"sha256": ledger_sha, "bytes": ledger_length,
                             "pinned": args.ledger_sha256 is not None}
        if args.ledger_sha256 and ledger_sha != expected_hash(args.ledger_sha256):
            raise Rejected("ledger_hash_mismatch", "Input ledger differs from the requested frozen SHA256")
        resolver = Resolver(args.asset_root, args.root_map)
        if resolver.map_sha256:
            summary["root_map_sha256"] = resolver.map_sha256
        with tempfile.TemporaryDirectory(prefix=".staging-", dir=output) as temporary:
            staging = Path(temporary)
            with closing(sqlite3.connect(staging / "entries.sqlite")) as index:
                summary["ledger_format"] = {}
                index_ledger(index, args.ledger, resolver, audit, args.ledger_field, summary["ledger_format"])
                audit_files(index, audit, None if args.audit_only else budget)
                if not audit.errors:
                    # Check input binding again in case the ledger changed while it was read.
                    if digest_file(args.ledger)[0] != ledger_sha:
                        raise Rejected("changed_during_export", "Ledger changed during audit")
                    write_inventory(index, staging / "FILES.jsonl.gz")
                    packages = [] if args.audit_only else make_packages(index, staging, budget)
                    manifest_sha, manifest_size = digest_file(staging / "FILES.jsonl.gz")
                    summary["inventory"] = {"path": "FILES.jsonl.gz", "sha256": manifest_sha,
                                            "bytes": manifest_size}
                    if not args.audit_only:
                        write_json(staging / "PACKAGES.json", {"schema": "frozen-assets-packages-v1",
                                   "complete": True,
                                   "files_manifest": {"file": "FILES.jsonl.gz", "sha256": manifest_sha,
                                                      "bytes": manifest_size},
                                   "ledger_sha256": ledger_sha, "inventory_sha256": manifest_sha,
                                   "mathematical_verification": "not_performed", "packages": packages})
                    # The temporary SQLite database is deliberately not exported.
            if not audit.errors:
                for built in staging.iterdir():
                    if built.name != "entries.sqlite":
                        built.rename(output / built.name)
                        published.append(output / built.name)
                summary["complete"] = True
                summary["publishable_bundle"] = not args.audit_only
                summary["packages"] = len(packages)
    except (Rejected, OSError, UnicodeError, sqlite3.Error, zipfile.BadZipFile) as exc:
        summary["complete"] = False
        summary["publishable_bundle"] = False
        for partial in published:
            try:
                partial.unlink()
            except OSError:
                pass
        if not isinstance(exc, Rejected):
            exc = Rejected("io_failure", "Could not read inputs or finish the export")
        audit.reject(exc)
    summary.update({"ledger_rows": audit.rows, "duplicate_rows": audit.duplicates,
                    "verified_files": audit.verified_files, "verified_bytes": audit.verified_bytes,
                    "errors": dict(audit.errors), "error_examples": audit.examples})
    write_json(output / "SUMMARY.json", summary)
    print(json.dumps({key: summary[key] for key in ("complete", "mode", "verified_files", "verified_bytes", "errors")},
                     ensure_ascii=False))
    return 0 if summary["complete"] else 1


if __name__ == "__main__":
    sys.exit(main())
