"""Structural cross-check against the already-closed n21 core inventory.

No n21 optimality is used as a lower-bound premise for n24. This compares
finite labeled triangulations and canonical codes only, retaining all frozen
n21 inputs unchanged.
"""
from pathlib import Path
from itertools import product
import argparse
import json
from positive_core_completion_synthesis import omitted_regions, triangulations, disk_check
from group_catalog import canonical_full
from stream_catalog import Catalog, sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def read(path):
    return json.loads(Path(path).read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    systempath = ROOT.parent / "round2-grouped/evidence/n21-interfaces-resume2/core-system.json"
    map_path = ROOT.parent / "evidence/n21-core-embedding-map.json"
    catalogpath = ROOT.parent / "evidence/n21-peeling-round5-B13-B14/N21-B13-dfs.json"
    system, originalmap = read(systempath), read(map_path)
    assert system["N"] == 21 and system["B"] == 13
    active = {tuple(sorted(f)) for f in system["active_faces"]}
    full = {tuple(sorted(f)) for f in system["all_faces"]}
    assert disk_check(21, 13, full)
    regions = omitted_regions(full, active)
    assert sorted(len(row["cycle"]) for row in regions) == [3]*8+[5]
    assert sorted(v for row in regions for v in row["interior"]) == [18]
    assert set(range(21))-{v for f in active for v in f} == {18}
    constructed = set()
    for place in range(len(regions)):
        choices = [triangulations(tuple(row["cycle"]), (18,) if i == place else ())
                   for i, row in enumerate(regions)]
        for replacements in product(*choices):
            proposed = frozenset(active).union(*replacements)
            assert active <= proposed and disk_check(21, 13, proposed)
            constructed.add(proposed)
    assert len(constructed) == 21+8*5 == 61 and frozenset(full) in constructed
    def code(faces):
        return canonical_full(21, 13, sorted(sum(1 << v for v in f) for f in faces))
    constructed_codes = {code(faces) for faces in constructed}
    assert len(constructed_codes) == 30
    assert originalmap["verified"] and originalmap["catalog_sha256"] == sha(catalogpath)
    indices = {row["index"] for row in originalmap["explicit_maps"]}
    assert len(indices) == len(originalmap["explicit_maps"]) == 30
    selected_codes = set()
    found = set()
    catalog = Catalog(catalogpath)
    assert catalog.header["N"] == 21 and catalog.header["B"] == 13 and catalog.header["orbits"] == 583857
    for index, row in catalog.rows():
        if index not in indices:
            continue
        faces = {tuple(v for v in range(21) if mask >> v & 1) for mask in row["faces"]}
        assert disk_check(21, 13, faces)
        selected_codes.add(code(faces))
        found.add(index)
    assert catalog.finished and found == indices
    assert selected_codes == constructed_codes
    n24path = ROOT / "evidence/positive-core-completion-synthesis-resume2.json"
    n24 = read(n24path)
    assert n24["verified"] and n24["n24"]["constructed_labeled_completions"] == 51
    assert n24["n24"]["distinct_listed_full_canonical_codes"] == 25
    assert sorted(len(row["cycle"]) for row in n24["n24"]["omitted_regions"]) == [3]*6+[5]
    sources = (systempath, map_path, catalogpath, n24path,
               ROOT / "positive_core_completion_synthesis.py", ROOT / "group_catalog.py",
               ROOT / "stream_catalog.py", Path(__file__))
    report = {"verified": True,
              "pattern": "one unused interior vertex, one pentagon, q triangle holes",
              "constructive_labeled_count": "21+5q",
              "n21": {"N": 21, "B": 13, "q": 8, "free_center": 18,
                      "labeled_completions": 61, "canonical_codes": 30,
                      "previous_paid_core_catalogue_indices": sorted(indices),
                      "all_constructed_disks_checked": True,
                      "canonical_set_equals_all_30_previously_paid_core_types": True},
              "n24": {"N": 24, "B": 15, "q": 6, "free_center": 19,
                      "labeled_completions": 51, "canonical_codes": 25,
                      "all_possible_abstract_embeddings_classified": False,
                      "entire_n24_catalogue_membership_verified": False},
              "n21_optimality_not_used_as_n24_lower_bound": True,
              "files_absolute": {str(path.resolve()): sha(path) for path in sources},
              "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
              "scope": "constructive free-center completion pattern and exact n21 inventory equality"}
    with args.output.open("x", encoding="utf8") as stream:
        json.dump(report, stream, indent=2)
    print("Free-center pattern exact PASS: n21 61 labeled / 30 canonical equals all old paid core types;",
          "same constructive rule gives n24 51 / 25; no n24 global classification", flush=True)


if __name__ == "__main__":
    main()
