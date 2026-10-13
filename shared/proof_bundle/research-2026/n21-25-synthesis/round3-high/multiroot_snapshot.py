"""Immutable streamed snapshot bindings with explicit workspace/bulk roots.

No file is moved, deleted, or overwritten. Hash integrity is separate from
mathematical validity. Root aliases can be relocated for independent replay.
"""
from pathlib import Path, PurePosixPath
import json
import time
from stream_catalog import sha

assert __debug__


class Bindings:
    def __init__(self, stream, roots):
        self.stream = stream
        self.roots = {name: Path(path).resolve() for name, path in roots.items()}
        assert self.roots and all(name.isascii() and name.isidentifier() for name in self.roots)
        assert all(path.is_dir() for path in self.roots.values())
        self.parents = {}
        self.seen = {}
        self.count = 0
        self.started = time.monotonic()

    def add(self, path, expected=None):
        path = Path(path).absolute()
        parentkey = str(path.parent)
        if parentkey not in self.parents:
            self.parents[parentkey] = path.parent.resolve()
        canonical = self.parents[parentkey] / path.name
        assert canonical.is_file() and not canonical.is_symlink()
        matches = [(name, root) for name, root in self.roots.items() if canonical.is_relative_to(root)]
        assert len(matches) == 1, "file must belong to exactly one declared snapshot root"
        name, root = matches[0]
        key = name+"/"+canonical.relative_to(root).as_posix()
        digest = sha(canonical)
        assert expected is None or digest == expected, ("changed proof input", str(canonical))
        if key in self.seen:
            assert self.seen[key] == digest, "input changed within a snapshot run"
            return digest
        if self.count:
            self.stream.write(",\n")
        self.stream.write("    "+json.dumps(key)+": "+json.dumps(digest))
        self.seen[key] = digest
        self.count += 1
        if self.count % 10000 == 0:
            self.stream.flush()
            print("Cross-volume proof files bound", self.count,
                  "seconds", round(time.monotonic()-self.started, 1), flush=True)
        return digest


def relative_key(key):
    assert type(key) is str and "\\" not in key and ":" not in key
    posix = PurePosixPath(key)
    assert not posix.is_absolute() and ".." not in posix.parts
    assert key == posix.as_posix() and len(posix.parts) >= 2
    return posix.parts[0], Path(*posix.parts[1:])
