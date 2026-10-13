"""Exact source lemma: each 20-face endpoint already forces the full skeleton.

For N=25,B=16 a simple disk triangulation has E=3N-B-3=56 and F=32.
The retained face edges plus boundary already have all 56 edges. They have
exactly 32 triangular cliques, all original faces, so no other completion is
possible. This is not an unrestricted geometric lower bound.
"""
from pathlib import Path
from itertools import combinations
import argparse
import json
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    path = ROOT / "evidence/n25-endpoint-core-isolation-resume1/REPORT.json"
    geometrypath = ROOT / "evidence/n25-isolation-exact-resume1/rotated-geometry.json"
    report, geometry = read(path), read(geometrypath)
    assert report["verified"] and report["geometry_sha256"] == sha(geometrypath)
    B, N = 16, 25
    full = {tuple(sorted(face)) for face in geometry["faces"]}
    assert len(full) == 2*N-B-2 == 32
    boundary = {tuple(sorted((i, (i+1) % B))) for i in range(B)}
    full_edges = boundary | {pair for face in full for pair in combinations(face, 2)}
    records = []
    for core in report["cores"]:
        retained = {tuple(sorted(face)) for face in core["faces"]}
        assert core["verified"] and len(retained) == 20 and retained <= full
        edges = boundary | {pair for face in retained for pair in combinations(face, 2)}
        assert len(edges) == 3*N-B-3 == 56 and edges == full_edges
        cliques = {triple for triple in combinations(range(N), 3)
                   if all(pair in edges for pair in combinations(triple, 2))}
        assert cliques == full and len(cliques) == 32
        missing = full-retained
        assert len(missing) == 12
        assert all(len(set(a)&set(b)) <= 1 for a, b in combinations(missing, 2))
        records.append({"parameter_sign": core["parameter_sign"],
                        "retained_faces": sorted(map(list, retained)),
                        "center_edges_with_boundary": sorted(map(list, edges)),
                        "center_edge_count": 56, "all_triangular_cliques": sorted(map(list, cliques)),
                        "triangular_clique_count": 32,
                        "removed_faces": sorted(map(list, missing)),
                        "no_removed_faces_share_an_edge": True,
                        "full_completion_unique_with_same_25_vertices_and_16_boundary": True})
    result = {"verified": True, "N": N, "B": B, "cores": records,
              "both_sparse_rod_cores_keep_full_center_skeleton": True,
              "same_order_topology_completion_family_not_enlarged": True,
              "statement_requires_an_explicit_core_embedding_into_a_simple_disk_triangulation": True,
              "endpoint_report_sha256": sha(path), "geometry_sha256": sha(geometrypath),
              "source_sha256": sha(Path(__file__)), "global_optimality_proved": False,
              "scope": "exact center-skeleton/completion lemma, not all 25-center covers"}
    args.output.write_text(json.dumps(result, indent=2), encoding="utf8")
    print("N25 sparse rod core completion lemma PASS: both keep all 56 center edges;",
          "32 cliques force unique full completion; no expanded same-n topology family", flush=True)


if __name__ == "__main__":
    main()
