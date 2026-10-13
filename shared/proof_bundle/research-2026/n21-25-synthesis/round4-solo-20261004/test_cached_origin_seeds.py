"""Actual N25 paid and attaining fixed-collar controls; no boundary-family claim."""
from pathlib import Path
import argparse
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import canonical, validate
from n25_outer_search import read, publish, bind, unchanged
from family_sparse_gate import sparse_library_gate
from complete_simple_collar import simple_holes, budgets
from cached_support_gate import derivation_gate
from test_origin_collar import native, relative, terminal
from test_streamed_collar import codes_from_union
from merge_origin_collar_chunks import merge

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    files = derivation_gate()
    derivation_path = ROOT / "cached-origin-seed-source-derivation.json"
    derived = read(derivation_path)
    assert derived["verified"] and derived["source_sha256"] == sha(ROOT / "derive_cached_origin_seed.py")
    for record in derived["files"]:
        source, target = ROOT / record["source"], ROOT / record["target"]
        assert sha(source) == record["source_sha256"] and sha(target) == record["target_sha256"]
        text = source.read_text(encoding="utf8")
        for before, after in record["changes"]:
            assert text.count(before) == 1
            text = text.replace(before, after)
        assert text == target.read_text(encoding="utf8")
        bind(files, source);bind(files, target)
    library_path = ROOT / "n25-B16-offline-union-sparse-library-20261005-v1/LIBRARY.json"
    constants, library, table, dependencies = sparse_library_gate(library_path)
    files.update(dependencies)
    assert library["B"] == 16 and library["obstacle_count"] == 164
    candidate_path = ROOT / "n25-B16-candidate-simple-hole-completions-20261005-v1/INPUT-COLLAR.json"
    candidate = read(candidate_path)
    source_groups_path = ROOT / "n25-B16-origin-slab0-prefix64-exact-20261005-v1/GROUPS.json"
    paid = read(source_groups_path)["groups"][0]
    assert (candidate["N"], candidate["B"]) == (25, 16)
    output.mkdir()
    cases = []
    for name, row, must_pay in (("known-attaining", candidate, False),
                                ("real-exact-strict-source", paid, True)):
        centers, faces, B = row["centers"], row["faces"], 16
        code, mapping = canonical(centers, B, faces, 1)
        assert list(code) == faces
        holes = simple_holes(centers, B, faces)
        allocations = list(budgets(25-centers, len(holes)))
        assert allocations
        for allocation_index, allocation in enumerate(allocations):
            results = []
            for flag in (0, 1):
                directory = output / f"{name}-allocation{allocation_index}-origin{flag}"
                directory.mkdir()
                tokens = [25, 16, centers, len(faces), *faces, len(holes)]
                for boundary, inside in zip(holes, allocation, strict=True):
                    tokens.extend([len(boundary), inside, *boundary])
                input_path = directory / "INPUT.tsv"
                input_path.write_text("\t".join(map(str, tokens))+"\n", encoding="ascii")
                manifest_path = directory / "MANIFEST.json"
                result = native("seed_cached_support_origin-linux", [
                    relative(input_path), relative(manifest_path), flag, 7, relative(table)])
                terminal(result, manifest_path, directory)
                assert result.returncode == 0, (result.returncode, result.stderr)
                manifest = read(manifest_path)
                assert manifest["seeded_fixed_collar_restriction"] and manifest["not_a_complete_boundary_family"]
                assert manifest["sparse_patterns_loaded"] == 164
                union = merge(manifest_path, 0, directory / "UNION")
                _, actual = codes_from_union(directory / "UNION/CATALOG.jsonl")
                expected = set() if must_pay else {code}
                assert actual == expected
                if must_pay:
                    assert manifest["sparse_proof_prunes"] > 0 and manifest["sparse_payments"]
                else:
                    assert manifest["sparse_proof_prunes"] == 0
                for payment in manifest["sparse_payments"]:
                    obstacle = library["obstacles"][payment["obstacle"]]
                    mapping = {key: payment[key] for key in ("centers", "anchors", "orientation", "shift")}
                    validate(centers, 16, obstacle["faces"], mapping, payment["sample_faces"])
                results.append(actual)
                cases.append({
                    "name": name, "allocation": allocation, "flag": flag, "N": 25, "B": 16,
                    "centers": centers, "expected_paid_or_retained_set_checked": True,
                    "residual_weak_graphs": len(actual), "sparse_prunes_not_type_count": manifest["sparse_proof_prunes"],
                    "manifest_sha256": sha(manifest_path), "union_sha256": sha(directory / "UNION/VERIFIED.json"),
                    "not_a_complete_boundary_family": True,
                })
                for path in (input_path, manifest_path, directory / "NATIVE-TERMINAL.json",
                             directory / "UNION/VERIFIED.json", directory / "UNION/CATALOG.jsonl"):
                    bind(files, path)
            assert results[0] == results[1]
    for path in (Path(__file__), candidate_path, source_groups_path, derivation_path, library_path,
                 ROOT / "seed_cached_support_origin-linux", ROOT / "derive_cached_origin_seed.py",
                 ROOT / "UNEXPOSED-ORIGIN-CENTER-SOURCE.md"):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "cached-support-actual-N25-fixed-seed-controls-v1",
        "N": 25, "B": 16, "cases": cases, "all_exact_attaining_seed_results_retained": True,
        "all_strict_source_seed_results_explicitly_paid": True,
        "origin_on_off_actual_N25_results_equal_when_both_have_unexposed_center": True,
        "not_a_complete_boundary_family": True, "library_sha256": sha(library_path),
        "source_sha256": sha(Path(__file__)),
        "seed_binary_sha256": sha(ROOT / "seed_cached_support_origin-linux"),
        "files_relative_to_workspace": files, "global_optimality_proved": False,
    })
    print("Cached-origin actual N25 fixed seeds PASS:", len(cases),
          "complete restricted controls; attaining retained, strict graph paid", flush=True)


if __name__ == "__main__":
    main()
