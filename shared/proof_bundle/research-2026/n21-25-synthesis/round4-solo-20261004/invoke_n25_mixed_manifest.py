"""Invoke the frozen mixed accepter in a fresh process without a long Windows argv."""
from pathlib import Path
import argparse
import runpy
import sys

from n25_outer_search import read
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", type=Path, required=True)
    args = ap.parse_args()
    manifestpath = args.manifest.resolve()
    assert manifestpath.is_relative_to(ROOT)
    data = read(manifestpath)
    assert data["schema"] == "N25-mixed-parent-frozen-argument-manifest-v1"
    auditpath = ROOT / "audit_n25_parent_mixed_supplements.py"
    assert sha(auditpath) == data["audit_source_sha256"]
    argv = [str(auditpath)]
    for name in ("snapshot", "base", "controls", "output"):
        path = Path(data[name]).resolve()
        assert path.is_relative_to(ROOT)
        argv.extend(["--"+name, str(path)])
    assert not Path(data["output"]).exists()
    for item in data["additions"]:
        assert len(item) == 4 and type(item[0]) is int and item[0] >= 0
        paths = [Path(value).resolve() for value in item[1:]]
        assert all(path.is_relative_to(ROOT) for path in paths)
        argv.extend(["--addition", str(item[0]), *map(str, paths)])
    assert data["nonstrict"]
    for item in data["nonstrict"]:
        assert len(item) == 2
        paths = [Path(value).resolve() for value in item]
        assert all(path.is_relative_to(ROOT) for path in paths)
        argv.extend(["--nonstrict", *map(str, paths)])
    sys.argv = argv
    runpy.run_path(str(auditpath), run_name="__main__")


if __name__ == "__main__":
    main()
