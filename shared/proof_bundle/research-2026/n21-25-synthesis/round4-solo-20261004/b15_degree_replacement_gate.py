"""Preserve origin mathematics and require the actual current-job terminal."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from stream_catalog import sha
from n25_outer_search import bind, unchanged
from b15_origin_replacement_gate import b15_origin_controls_gate
from pending_degree_production_gate import production_gate

assert __debug__


def b15_degree_replacement_gate(controlspath, previous, B):
    assert B == 15
    files = b15_origin_controls_gate(controlspath)
    files.update(production_gate(
        ROOT / "n25-B15-offline-contracted-union27-library-20261005-v1/LIBRARY.json",
        ROOT / "n25-B15-union27-sparse-map-controls-20261005-v1/VERIFIED.json",
        ROOT / "n25-B15-union27-eight-sparse-guard-controls-20261005-v1/VERIFIED.json", B))
    from b15_degree_controlled_stop import replacement_readiness
    files.update(replacement_readiness(previous))
    for path in (Path(__file__), ROOT / "b15_degree_controlled_stop.py",
                 ROOT / "pending_degree_production_gate.py"):
        bind(files, path)
    unchanged(files)
    return files
