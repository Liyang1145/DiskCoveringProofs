"""Reassemble and check the n=26 certificate archive without network access."""

import argparse
import hashlib
import json
import tempfile
import zipfile
from pathlib import Path, PurePosixPath


ROOT = Path(__file__).resolve().parent
BLOCK = 1024 * 1024


def require(condition, message):
    if not condition:
        raise ValueError(message)


def local_path(root, name):
    relative = PurePosixPath(name)
    require(relative.parts and relative.as_posix() == name and not relative.is_absolute()
            and ".." not in relative.parts and "\\" not in name and ":" not in name,
            f"Invalid manifest path {name!r}")
    path = root.joinpath(*relative.parts)
    require(path.resolve().is_relative_to(root), f"Path leaves the destination: {name}")
    return path


def copy_checked(source, destination, entry, label, combined=None):
    digest = hashlib.sha256()
    size = 0
    for block in iter(lambda: source.read(BLOCK), b""):
        size += len(block)
        require(size <= entry["bytes"], f"Wrong size for {label}")
        digest.update(block)
        if combined is not None:
            combined.update(block)
        destination.write(block)
    require(size == entry["bytes"] and digest.hexdigest() == entry["sha256"],
            f"Size or SHA-256 mismatch for {label}")
    return size


def assemble(parts_dir, manifest, joined):
    digest = hashlib.sha256()
    size = 0
    archive = manifest["archive"]
    parts = manifest["parts"]
    require(parts, "The certificate manifest has no parts")
    for i, entry in enumerate(parts, start=1):
        name = entry["file"]
        require(name == f"{archive['name']}.part{i:03d}", "Unexpected part order")
        with local_path(parts_dir, name).open("rb") as source:
            size += copy_checked(source, joined, entry, name, digest)
    require(size == archive["bytes"] and digest.hexdigest() == archive["sha256"],
            "Reassembled archive differs from the manifest")
    joined.seek(0)


def restore(joined, manifest, destination):
    entries = manifest["members"]
    targets = {entry["path"]: local_path(destination, entry["path"]) for entry in entries}
    with zipfile.ZipFile(joined) as archive:
        names = archive.namelist()
        require(len(names) == len(entries) == len(targets) and set(names) == targets.keys(),
                "Archive members differ from the manifest")
        pending = []
        for entry in entries:
            name = entry["path"]
            path = targets[name]
            require(archive.getinfo(name).file_size == entry["bytes"], f"Wrong ZIP size for {name}")
            if path.exists():
                with path.open("rb") as existing:
                    digest = hashlib.file_digest(existing, "sha256").hexdigest()
                require(path.stat().st_size == entry["bytes"] and digest == entry["sha256"],
                        f"Refusing to replace differing content: {name}")
            else:
                pending.append((entry, path))
        for entry, path in pending:
            path.parent.mkdir(parents=True, exist_ok=True)
            with tempfile.NamedTemporaryFile(dir=path.parent, suffix=".restoring", delete=False) as output:
                temporary = Path(output.name)
            try:
                with archive.open(entry["path"]) as source, temporary.open("wb") as output:
                    copy_checked(source, output, entry, entry["path"])
                require(not path.exists(), f"Destination appeared during restoration: {entry['path']}")
                temporary.rename(path)
            finally:
                temporary.unlink(missing_ok=True)
    return len(pending)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--destination", type=Path, default=ROOT)
    args = parser.parse_args()
    parts_dir = (ROOT / "certificates").resolve()
    manifest = json.loads((parts_dir / "manifest.json").read_text(encoding="utf-8"))
    require(manifest["format"] == "n26-certificate-shards-v1", "Unsupported manifest format")
    with tempfile.TemporaryFile() as joined:
        assemble(parts_dir, manifest, joined)
        count = restore(joined, manifest, args.destination.resolve())
    print(f"PASS {len(manifest['parts'])} shard hashes, archive SHA-256, "
          f"and {len(manifest['members'])} certificate files ({count} restored)")


if __name__ == "__main__":
    main()
