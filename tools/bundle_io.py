"""Lossless multipart gzip readers. No mathematical proof acceptance."""
import hashlib
import io
from pathlib import Path


def safe_asset_path(root, name):
    if not isinstance(name, str) or not name or "\\" in name:
        raise ValueError("Noncanonical relative asset path")
    relative = Path(name)
    if relative.is_absolute() or ".." in relative.parts or ":" in relative.parts[0]:
        raise ValueError("Unsafe relative asset path")
    root = Path(root).resolve()
    path = (root / relative).resolve()
    if root not in path.parents:
        raise ValueError("Asset escapes repository root")
    return path


def sha256_file(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


class PartsReader(io.RawIOBase):
    def __init__(self, paths):
        self.paths = iter(paths)
        self.stream = None
        self._advance()

    def _advance(self):
        if self.stream:
            self.stream.close()
        path = next(self.paths, None)
        self.stream = open(path, "rb") if path is not None else None

    def readable(self):
        return True

    def readinto(self, target):
        while self.stream is not None:
            count = self.stream.readinto(target)
            if count:
                return count
            self._advance()
        return 0

    def close(self):
        if self.stream:
            self.stream.close()
        super().close()
