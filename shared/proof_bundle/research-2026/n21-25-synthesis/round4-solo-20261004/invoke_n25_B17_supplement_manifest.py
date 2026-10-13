"""Invoke the unchanged exact adopter without Windows command-line truncation."""
from pathlib import Path
import argparse
import runpy
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from n25_outer_search import read
from stream_catalog import sha

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", type=Path, required=True)
    args = ap.parse_args()
    manifestpath = args.manifest.resolve()
    assert manifestpath.is_relative_to(ROOT)
    manifest = read(manifestpath)
    assert (manifest["N"], manifest["B"]) == (25, 17)
    accepter = ROOT / "audit_n25_parent_direct_supplements.py"
    assert manifest["adopter_source_sha256"] == sha(accepter)
    for path, digest in manifest["frozen_files"].items():
        assert sha(path) == digest
    argv = [str(accepter)]
    for key in ("snapshot", "base", "controls", "output"):
        path = Path(manifest[key]).resolve()
        assert path.is_relative_to(ROOT)
        argv.extend(["--"+key, str(path)])
    seen = set()
    for addition in manifest["additions"]:
        pid = addition["parent_index"]
        assert type(pid) is int and pid not in seen
        seen.add(pid)
        argv.extend(["--addition", str(pid), addition["family"],
                     addition["proof_path"], addition["exact_path"]])
    assert seen
    sys.argv = argv
    runpy.run_path(str(accepter), run_name="__main__")


if __name__ == "__main__":
    main()
