# SPDX-License-Identifier: MIT
"""Download optional frozen bundles and restore only hash-bound asset files.

Use a PACKAGES.json pinned by the repository delivery manifest. This is a byte
restorer, not a mathematical checker. Source files and differing destination
files are never overwritten. The ZIP layout is assets/<canonical>.
"""
import argparse
from contextlib import closing
import gzip
import hashlib
import json
from pathlib import Path
import sqlite3
import stat
import tempfile
from urllib.parse import quote, urlsplit
from urllib.request import urlopen
import zipfile

from export_frozen_assets import Rejected, digest_file, expected_hash, load_json, safe_relative


def require(condition, message):
    if not condition:
        raise ValueError(message)


def size_value(value):
    require(type(value) is int and value >= 0, "Invalid byte length")
    return value


def filename(value):
    safe_relative(value)
    require("/" not in value, "Package file must be a basename")
    return value


def checked_file(path, expected):
    require(path.is_file(), "Missing package file: " + path.name)
    require(path.stat().st_size == size_value(expected["bytes"]), "Package size mismatch: " + path.name)
    sha, size = digest_file(path)
    require(sha == expected_hash(expected["sha256"]), "Package SHA256 mismatch: " + path.name)
    return path


def acquire(entry, directory, base_url):
    name = filename(entry["file"])
    size_value(entry["bytes"])
    expected_hash(entry["sha256"])
    path = directory / name
    if path.exists() or not base_url:
        return checked_file(path, entry)
    directory.mkdir(parents=True, exist_ok=True)
    print("Downloading " + name, flush=True)
    with tempfile.NamedTemporaryFile(dir=directory, prefix="download-", suffix=".part", delete=False) as stream:
        temporary = Path(stream.name)
        count = 0
        digest = hashlib.sha256()
        try:
            with urlopen(base_url.rstrip("/") + "/" + quote(name), timeout=30) as source:
                for block in iter(lambda: source.read(1024 * 1024), b""):
                    count += len(block)
                    require(count <= entry["bytes"], "Downloaded package exceeds declared size")
                    digest.update(block)
                    stream.write(block)
            require(count == entry["bytes"], "Downloaded package length mismatch")
            require(digest.hexdigest() == entry["sha256"].lower(), "Downloaded package hash mismatch")
        except BaseException:
            stream.close()
            temporary.unlink(missing_ok=True)
            raise
    created = False
    try:
        # Exclusive creation prevents replacing a concurrently created cache file.
        with path.open("xb") as target, temporary.open("rb") as source:
            created = True
            for block in iter(lambda: source.read(1024 * 1024), b""):
                target.write(block)
    except BaseException:
        if created:
            path.unlink(missing_ok=True)
        raise
    finally:
        temporary.unlink(missing_ok=True)
    return checked_file(path, entry)


def asset_target(root, canonical):
    safe_relative(canonical)
    target = (root / "assets" / Path(*canonical.split("/"))).resolve()
    require(root in target.parents, "Asset escapes destination")
    return target


def restore(index_path, package_dir, destination, base_url=None):
    index = load_json(Path(index_path).read_text(encoding="utf-8-sig"))
    require(index.get("schema") == "frozen-assets-packages-v1", "Unsupported package index schema")
    require(index.get("complete") is True, "Bundle index is incomplete")
    require(index.get("mathematical_verification") == "not_performed", "Unexpected bundle verification scope")
    packages = index.get("packages")
    require(isinstance(packages, list) and bool(packages), "Empty package list")
    directory, root = Path(package_dir).resolve(), Path(destination).resolve()
    names = set()
    for entry in [index["files_manifest"], *packages]:
        name = filename(entry["file"])
        require(name.casefold() not in names, "Duplicate package filename")
        names.add(name.casefold())
    ledger_path = acquire(index["files_manifest"], directory, base_url)
    # A disk index permits restoring million-file closures without a huge dict.
    with tempfile.TemporaryDirectory(prefix="frozen-restore-") as temporary:
        with closing(sqlite3.connect(str(Path(temporary) / "files.sqlite"))) as database:
            database.execute("CREATE TABLE files(path TEXT PRIMARY KEY, folded TEXT UNIQUE, sha TEXT, bytes INTEGER, seen INTEGER DEFAULT 0)")
            count, total_bytes = 0, 0
            with gzip.open(ledger_path, "rt", encoding="utf-8") as stream:
                for line in stream:
                    entry = load_json(line)
                    name = safe_relative(entry["canonical"])
                    sha = expected_hash(entry["sha256"])
                    size = size_value(entry["bytes"])
                    database.execute("INSERT INTO files(path,folded,sha,bytes) VALUES (?,?,?,?)", (name, name.casefold(), sha, size))
                    count += 1
                    total_bytes += size
            require(count > 0, "Empty file ledger")
            require(sum(size_value(p["files"]) for p in packages) == count, "Package file count differs from ledger")
            database.commit()
            restored = 0
            for entry in packages:
                archive_path = acquire(entry, directory, base_url)
                with zipfile.ZipFile(archive_path) as archive:
                    members = archive.infolist()
                    require(len(members) == entry["files"], "Unexpected archive member count")
                    raw_bytes = 0
                    for member in members:
                        require(member.filename.startswith("assets/"), "Unbound archive member")
                        require(not member.is_dir(), "Unexpected directory member")
                        mode = member.external_attr >> 16
                        require(not stat.S_ISLNK(mode), "Symlink archive member")
                        canonical = safe_relative(member.filename[len("assets/"):])
                        row = database.execute("SELECT sha,bytes,seen FROM files WHERE path=?", (canonical,)).fetchone()
                        require(row is not None, "Archive contains a file outside the ledger")
                        sha, size, seen = row
                        require(not seen, "Duplicate archive member")
                        require(member.file_size == size, "Archive member length differs from ledger")
                        target = asset_target(root, canonical)
                        if target.exists():
                            actual_sha, actual_size = digest_file(target)
                            require((actual_sha, actual_size) == (sha, size), "Refusing differing existing asset: " + canonical)
                        else:
                            target.parent.mkdir(parents=True, exist_ok=True)
                            digest, written = hashlib.sha256(), 0
                            created = False
                            try:
                                with target.open("xb") as output:
                                    created = True
                                    with archive.open(member) as source:
                                        for block in iter(lambda: source.read(1024 * 1024), b""):
                                            written += len(block)
                                            require(written <= size, "Member exceeds frozen size")
                                            digest.update(block)
                                            output.write(block)
                                require(written == size and digest.hexdigest() == sha, "Restored member SHA256 mismatch")
                            except BaseException:
                                if created:
                                    target.unlink(missing_ok=True)
                                raise
                        database.execute("UPDATE files SET seen=1 WHERE path=?", (canonical,))
                        restored += 1
                        raw_bytes += size
                    require(raw_bytes == size_value(entry["uncompressed_bytes"]), "Package raw-byte count mismatch")
                database.commit()
                print(f"Restored bytes verified: {restored}/{count} files", flush=True)
            require(database.execute("SELECT count(*) FROM files WHERE seen=0").fetchone()[0] == 0, "Incomplete restored closure")
    return {"files": count, "bytes": total_bytes, "complete": True, "mathematical_verification": "not_performed"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package-index", required=True, type=Path)
    sources = parser.add_mutually_exclusive_group(required=True)
    sources.add_argument("--package-dir", type=Path)
    sources.add_argument("--from-url", help="HTTPS release download directory; index stays locally pinned")
    parser.add_argument("--cache", type=Path, default=Path("build/frozen-downloads"))
    parser.add_argument("--destination", required=True, type=Path)
    args = parser.parse_args()
    try:
        if args.from_url:
            url = urlsplit(args.from_url)
            require(url.scheme == "https" and bool(url.netloc), "Package download URL must use HTTPS")
        result = restore(args.package_index, args.package_dir or args.cache, args.destination, args.from_url)
    except (OSError, EOFError, ValueError, KeyError, TypeError, sqlite3.Error, zipfile.BadZipFile) as error:
        parser.exit(1, "FROZEN RESTORE FAILED: " + str(error) + "\n")
    print(json.dumps(result))
    print("Frozen asset byte restoration passed; no mathematical replay performed.")


if __name__ == "__main__":
    main()
