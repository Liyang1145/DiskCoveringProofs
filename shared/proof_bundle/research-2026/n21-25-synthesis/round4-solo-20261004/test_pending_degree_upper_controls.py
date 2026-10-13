"""Independent arithmetic, uncapped whole sets, audit order and N25 seeds."""
from pathlib import Path
import argparse
import random
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import canonical, validate
from n25_outer_search import read, publish, bind, unchanged
from family_sparse_gate import sparse_library_gate
from test_pending_degree_upper_small import derivation_gate
from test_cached_support_origin_partition import native_logged
from test_origin_collar import native, relative, terminal
from test_outer_collar import collar_codes
from test_streamed_collar import codes_from_union
from merge_origin_collar_chunks import merge
from complete_simple_collar import simple_holes, budgets

assert __debug__


def state_tokens(index, N, B, adjacency, pending):
    result = [index, N, B, len(pending), *adjacency]
    for boundary, inside in pending:
        result.extend([inside, len(boundary), *boundary])
    return result


def independent_upper_impossible(N, B, adjacency, pending):
    current_root_degree = adjacency[0].bit_count()
    for vertex in range(1, B):
        existing = {other for other in range(N) if adjacency[vertex] >> other & 1}
        budget = 0
        for boundary, inside in pending:
            if vertex in boundary:
                existing.update(boundary)
                budget += inside
        existing.discard(vertex)
        if min(N-1, len(existing)+budget) < current_root_degree:
            return True
    return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    main_derivation, original, target = derivation_gate()
    control_path = ROOT / "pending-degree-controls-source-derivation.json"
    control = read(control_path)
    assert control["verified"] and control["source_sha256"] == sha(ROOT / "derive_pending_degree_controls.py")
    files = {}
    for record in control["files"]:
        source, derived = ROOT / record["source"], ROOT / record["target"]
        assert sha(source) == record["source_sha256"] and sha(derived) == record["target_sha256"]
        text = source.read_text(encoding="utf8")
        for before, after in record["changes"]:
            assert text.count(before) == 1
            text = text.replace(before, after)
        assert text == derived.read_text(encoding="utf8")
        bind(files, source);bind(files, derived)
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    output.mkdir()
    rng = random.Random(2510051627)
    states = []
    # Empty pending; no remaining budget; enough budget; overlapping existing
    # vertices; pure internal region; equality (not a strict contradiction).
    adjacency = [0]*8
    for a, c in ((0, 1), (1, 2), (2, 3), (3, 0), (0, 4), (0, 5)):
        adjacency[a] |= 1 << c
        adjacency[c] |= 1 << a
    for pending in ([], [([1, 2, 3], 0)], [([1, 2, 3], 4)],
                    [([0, 1, 2], 0), ([0, 1, 3], 0)],
                    [([4, 5, 6], 1)], [([0, 1, 2, 3], 1)]):
        states.append((8, 4, adjacency, pending))
    for _ in range(500):
        N = rng.randrange(4, 26)
        B = rng.randrange(3, N+1)
        adjacency = [0]*N
        for a in range(N):
            for c in range(a+1, N):
                if rng.randrange(4) == 0:
                    adjacency[a] |= 1 << c
                    adjacency[c] |= 1 << a
        for a in range(B):
            c = (a+1) % B
            adjacency[a] |= 1 << c
            adjacency[c] |= 1 << a
        pending = []
        for _ in range(rng.randrange(0, min(N, 8))):
            length = rng.randrange(2, N+1)
            pending.append((rng.sample(range(N), length), rng.randrange(0, N+1)))
        states.append((N, B, adjacency, pending))
    expected = [independent_upper_impossible(*row) for row in states]
    assert any(expected) and not all(expected)
    tokens = [len(states)]
    for index, row in enumerate(states):
        tokens.extend(state_tokens(index, *row))
    probe_input = output / "ARITHMETIC-INPUT.tsv"
    probe_input.write_text("\t".join(map(str, tokens))+"\n", encoding="ascii")
    for flag in (0, 1):
        directory = output / f"arithmetic-flag-{flag}"
        directory.mkdir()
        report_path = directory / "RESULT.json"
        result = native("pending_degree_upper_probe-linux", [relative(probe_input), relative(report_path), flag])
        terminal(result, report_path, directory)
        assert result.returncode == 0
        report = read(report_path)
        assert report["functional_control_only"]
        assert report["answers"] == (expected if flag else [False]*len(expected))
        bind(files, report_path);bind(files, directory / "NATIVE-TERMINAL.json")
    whole_cases = []
    # No geometric screen/library: compare entire original necessary sets.
    for N, B in ((7, 4), (8, 5)):
        for mode in ("noscreen", "audit-noscreen"):
            observed = []
            for flag in (0, 1):
                directory = output / f"N{N}-B{B}-{mode}-flag{flag}"
                directory.mkdir()
                manifest_path = directory / "MANIFEST.json"
                code, seconds = native_logged("peel_pending_degree_origin_collar-linux", [
                    N, B, relative(manifest_path), constants["angle_scale"], *constants["angle_caps"],
                    0, mode, "-", "-", 4058615, 7, 0, flag,
                ], directory)
                assert code == 0
                manifest = read(manifest_path)
                merge(manifest_path, code, directory / "UNION")
                _, actual = codes_from_union(directory / "UNION/CATALOG.jsonl")
                observed.append(actual)
                whole_cases.append({"N": N, "B": B, "mode": mode, "flag": flag,
                                    "calls": manifest["calls"], "seconds": seconds,
                                    "weak_graphs": len(actual), "actual_exit_code": code})
                for path in (manifest_path, directory / "NATIVE-TERMINAL.json",
                             directory / "UNION/VERIFIED.json", directory / "UNION/CATALOG.jsonl"):
                    bind(files, path)
            assert observed[0] == observed[1]
            print("Pending degree full noscreen set equal:", N, B, mode, len(observed[0]), flush=True)
    library_path = ROOT / "n25-B15-offline-contracted-union27-library-20261005-v1/LIBRARY.json"
    _, library, table, dependencies = sparse_library_gate(library_path)
    files.update(dependencies)
    reference_root = ROOT / "n25-B15-union27-eight-sparse-guard-controls-20261005-v1"
    reference_control = read(reference_root / "VERIFIED.json")
    assert reference_control["verified"] and reference_control["library_sha256"] == sha(library_path)
    unchanged(reference_control["files_relative_to_workspace"])
    for N in (21, 22):
        reference_path = reference_root / f"N{N}-B15-eight-sparse-audit.json"
        declared = next(row for row in reference_control["cases"] if row["N"] == N and row["mode"] == "audit")
        assert sha(reference_path) == declared["residual_sha256"]
        _, expected_set = collar_codes(reference_path, N, 15)
        directory = output / f"N{N}-B15-audit-flag1"
        directory.mkdir()
        manifest_path = directory / "MANIFEST.json"
        code, seconds = native_logged("peel_pending_degree_origin_collar-linux", [
            N, 15, relative(manifest_path), constants["angle_scale"], *constants["angle_caps"],
            0, "audit", "-", relative(table), 4058615, 100000, 1, 1,
        ], directory)
        assert code == 0
        manifest = read(manifest_path)
        merge(manifest_path, code, directory / "UNION")
        _, actual = codes_from_union(directory / "UNION/CATALOG.jsonl")
        assert actual == expected_set
        whole_cases.append({"N": N, "B": 15, "mode": "audit", "flag": 1,
                            "calls": manifest["calls"], "seconds": seconds,
                            "weak_graphs": len(actual), "actual_exit_code": code,
                            "matches_original_complete_reference": True})
        for path in (reference_path, manifest_path, directory / "NATIVE-TERMINAL.json",
                     directory / "UNION/VERIFIED.json", directory / "UNION/CATALOG.jsonl"):
            bind(files, path)
        print("Pending degree full audit reference equal:", N, 15, len(actual), manifest["calls"], flush=True)
    library16_path = ROOT / "n25-B16-offline-union-sparse-library-20261005-v1/LIBRARY.json"
    _, library16, table16, dependencies16 = sparse_library_gate(library16_path)
    files.update(dependencies16)
    candidate_path = ROOT / "n25-B16-candidate-simple-hole-completions-20261005-v1/INPUT-COLLAR.json"
    paid_path = ROOT / "n25-B16-origin-slab0-prefix64-exact-20261005-v1/GROUPS.json"
    seed_cases = []
    for name, row, paid in (("known-attaining", read(candidate_path), False),
                            ("strict-source", read(paid_path)["groups"][0], True)):
        centers, faces, B = row["centers"], row["faces"], 16
        code, mapping = canonical(centers, B, faces, 1)
        assert list(code) == faces
        holes = simple_holes(centers, B, faces)
        for allocation_index, allocation in enumerate(budgets(25-centers, len(holes))):
            observed = []
            for flag in (0, 1):
                directory = output / f"{name}-allocation{allocation_index}-degree{flag}"
                directory.mkdir()
                tokens = [25, 16, centers, len(faces), *faces, len(holes)]
                for boundary, inside in zip(holes, allocation, strict=True):
                    tokens.extend([len(boundary), inside, *boundary])
                input_path = directory / "INPUT.tsv"
                input_path.write_text("\t".join(map(str, tokens))+"\n", encoding="ascii")
                manifest_path = directory / "MANIFEST.json"
                result = native("seed_pending_degree_origin-linux", [
                    relative(input_path), relative(manifest_path), 1, 7, relative(table16), flag])
                terminal(result, manifest_path, directory)
                assert result.returncode == 0
                manifest = read(manifest_path)
                assert manifest["seeded_fixed_collar_restriction"] and manifest["not_a_complete_boundary_family"]
                merge(manifest_path, result.returncode, directory / "UNION")
                _, actual = codes_from_union(directory / "UNION/CATALOG.jsonl")
                assert actual == (set() if paid else {code})
                if paid:
                    assert manifest["sparse_proof_prunes"] > 0
                else:
                    assert manifest["sparse_proof_prunes"] == manifest["pending_degree_upper_prunes_not_type_count"] == 0
                for payment in manifest["sparse_payments"]:
                    obstacle = library16["obstacles"][payment["obstacle"]]
                    validate(centers, B, obstacle["faces"],
                             {key: payment[key] for key in ("centers", "anchors", "orientation", "shift")},
                             payment["sample_faces"])
                observed.append(actual)
                seed_cases.append({"name": name, "allocation": allocation, "flag": flag,
                                   "actual_exit_code": result.returncode, "residual_weak_graphs": len(actual)})
                for path in (input_path, manifest_path, directory / "NATIVE-TERMINAL.json",
                             directory / "UNION/VERIFIED.json", directory / "UNION/CATALOG.jsonl"):
                    bind(files, path)
            assert observed[0] == observed[1]
    negatives = []
    for name, flag, limit in (("invalid-flag", 2, 0), ("incomplete-node-limit", 1, 1)):
        directory = output / name
        directory.mkdir()
        path = directory / "MANIFEST.json"
        result = native("peel_pending_degree_origin_collar-linux", [
            25, 15, relative(path), constants["angle_scale"], *constants["angle_caps"],
            limit, "dfs", "-", relative(table), 4058615, 7, 1, flag,
        ])
        terminal(result, path, directory)
        assert result.returncode != 0 and not path.exists()
        negatives.append(name)
        bind(files, directory / "NATIVE-TERMINAL.json")
    for path in (Path(__file__), control_path, main_derivation, original, target, probe_input,
                 constants_path, candidate_path, paid_path, reference_root / "VERIFIED.json",
                 library_path, library16_path, ROOT / "pending_degree_upper.inc",
                 ROOT / "PENDING-DEGREE-UPPER-SOURCE.md", ROOT / "pending_degree_upper_probe.cpp",
                 ROOT / "pending_degree_upper_probe-linux", ROOT / "peel_pending_degree_origin_collar-linux",
                 ROOT / "seed_pending_degree_origin-linux"):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "pending-degree-upper-arithmetic-whole-set-and-seed-controls-v1",
        "arithmetic_states_checked": len(states), "arbitrary_states_only_functional_controls": True,
        "whole_set_cases": whole_cases, "fixed_N25_seed_cases": seed_cases, "refusals": negatives,
        "known_N25_attaining_seed_explicitly_retained": True,
        "not_a_complete_N25_boundary_family": True,
        "not_a_production_replacement_or_stop_authorization": True,
        "source_sha256": sha(Path(__file__)), "files_relative_to_workspace": files,
        "global_optimality_proved": False,
    })
    print("Pending degree arithmetic, uncapped whole sets, audit and attaining controls PASS", flush=True)


if __name__ == "__main__":
    main()
