"""Replay existing n21 roots/upper/local/core-angle/six-disk inputs safely.

All fresh outputs go into a new directory.  Frozen milestones are read-only.
"""
from pathlib import Path
import argparse
import importlib.util
import json
import shutil
import sys

ROOT = Path(__file__).resolve().parent
SYN = ROOT.parent
N21 = SYN.parent / "n21-global"
assert __debug__


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    assert not out.exists()
    out.mkdir(parents=True)
    for name in ("core-root.json", "core-system.json", "candidate-numeric.json", "angle-constants.json"):
        shutil.copy2(N21 / "evidence" / name, out / name)
    root = load("resumed_exact_n21_root", N21 / "root_certificate.py")
    root.EV = out
    data, z, rho = root.verify()
    root.upper(data, z, rho)
    local = load("resumed_exact_n21_local", N21 / "local_isolation.py")
    local.EV = out
    local.main()
    assert (out / "local-isolation-certificate.json").read_bytes() == (
        N21 / "evidence" / "local-isolation-certificate.json").read_bytes()

    replay = load("resumed_core_tree_replay", SYN / "replay_results.py")
    replay.core_replay(out)
    # The six-disk module intentionally reconfigures the shared numeric/force
    # modules.  Perform it last, after the n21 core-angle tree has been checked.
    sys.path.insert(0, str(N21))
    six = load("resumed_six_lower_bound", N21 / "six_core_exclusion.py")
    # Restore the general rod construction: core_replay replaced G.edges with
    # a core-only closure.  Reusing that closure for a hexagon is invalid.
    def general_edges(b, faces):
        return ([(i, b+i) for i in range(b)] +
                [(i, b+(i+1) % b) for i in range(b)] +
                [(b+six.G.N+k, b+j) for k, face in enumerate(faces) for j in face])
    six.G.edges = general_edges
    six.EV = out
    (out / "peeling-round1").mkdir()
    shutil.copy2(N21 / "evidence/peeling-round1/N6-B6-noscreen.json",
                 out / "peeling-round1/N6-B6-noscreen.json")
    (out / "six-core-exclusion").mkdir()
    for i in range(3):
        shutil.copy2(N21 / f"evidence/six-core-exclusion/hexagon-{i}.json.gz",
                     out / f"six-core-exclusion/hexagon-{i}.json.gz")
    argv = sys.argv
    try:
        sys.argv = ["six_core_exclusion.py", "--replay"]
        six.main()
    finally:
        sys.argv = argv
    report = {"verified": True, "N": 21,
              "replayed": ["173D root", "entire closed disk upper", "92D anchor isolation",
                           "positive-core whole-angle tree", "six-disk auxiliary lower bound"],
              "global_optimality_proved_here": False}
    (out / "INTERFACES.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("N21 old interfaces freshly replayed without changing frozen inputs", flush=True)


if __name__ == "__main__":
    main()
