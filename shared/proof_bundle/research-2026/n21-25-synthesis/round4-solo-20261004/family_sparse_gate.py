"""Generic n25 sparse-library exact gate; no solver imported."""
from pathlib import Path
from fractions import Fraction as F
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
WORK = ROOT.parents[2].resolve()
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, bind, unchanged
from angle_obstructions import constants_gate

assert __debug__


def sparse_library_gate(path):
    library = read(path)
    assert library["verified"] and library["schema"] == "strict-sparse-outer-obstacle-library-v1"
    B = library["B"]
    assert library["source_N"] == 25 and B in (14, 15, 16, 17)
    assert library["all_library_trees_fresh_exact_replayed"] and library["no_root_or_local_theorem_used"]
    assert library["all_B_boundary_sites_and_2B_anchor_rods_preserved"]
    assert library["source_sha256"] == sha(ROOT / "export_family_sparse_library.py")
    table = path.parent / "OBSTACLES.tsv"
    assert sha(table) == library["pattern_table_sha256"]
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    constants_gate(constants)
    assert F(constants["radius_upper"]) == F(library["radius_threshold"]) == F(239146311738101, 10**15)
    assert constants["families"] == [[b, 25-b] for b in range(14, 18)]
    files = dict(library["files"])
    unchanged(files)
    lines = table.read_text(encoding="ascii").splitlines()
    assert lines[0] == library["schema"] and len(lines) == library["obstacle_count"]+1
    assert library["obstacle_count"] == len(library["obstacles"]) > 0
    for index, obstacle in enumerate(library["obstacles"]):
        assert obstacle["id"] == index and obstacle["B"] == B
        assert list(map(int, lines[index+1].split())) == [
            index, B, obstacle["centers"], len(obstacle["faces"]), *obstacle["faces"]]
        treepath = WORK / obstacle["tree_file_relative_to_workspace"]
        assert sha(treepath) == obstacle["tree_sha256"]
        with gzip.open(treepath, "rt", encoding="utf8") as stream:
            tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
        assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (
            25, B, obstacle["centers"], obstacle["faces"])
        assert tree["constants_sha256"] == sha(constants_path)
        assert all(node["kind"] in ("EMPTY", "SPLIT", "DUAL") for node in tree["nodes"])
        assert exact.verify(B, obstacle["centers"], obstacle["faces"], tree["nodes"], constants) == obstacle["fresh_exact_replay"]
    for p in (path, table, constants_path, Path(__file__), ROOT / "angle_obstructions.py",
              ROOT / "SHORT-PATH-ANGLE-CERTIFICATES.md", ROOT / "family-discovery-tool-derivation.json"):
        bind(files, p)
    return constants, library, table, files
