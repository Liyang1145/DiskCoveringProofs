"""Verify the exact outer-threshold derivation and all new obstacle maps."""
from pathlib import Path
import argparse
import json
import random
import subprocess
from audit_streamed_hierarchy import check_map
from paid_binary_residual import BinaryRows, verify_merge
from stream_catalog import sha, no_duplicate_keys
from test_paid_storage import check_stream_derivation

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parents[2].resolve()
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists() and not args.output.is_absolute() and args.output.as_posix().isascii()
    args.output.mkdir(parents=True)
    check_stream_derivation()
    kernel = (ROOT / "peel_paid_stream_kernel.inc").read_text(encoding="utf8")
    assert kernel.replace('#include "paid_matcher.inc"', '#include "paid_outer_matcher.inc"') == (
        ROOT / "peel_outer_stream_kernel.inc").read_text(encoding="utf8")
    matcher = (ROOT / "paid_matcher.inc").read_text(encoding="utf8")
    changes = [
        ("strict-obstacle-library-v1", "strict-outer-obstacle-library-v1"),
        ("pop(uint32_t(mask)&((uint32_t(1)<<B)-1))<2",
         "pop(uint32_t(mask)&((uint32_t(1)<<B)-1))<1"),
        ("pop(face&((uint32_t(1)<<b)-1))>=2",
         "pop(face&((uint32_t(1)<<b)-1))>=1"),
    ]
    for before, after in changes:
        assert matcher.count(before) == 1
        matcher = matcher.replace(before, after, 1)
    assert matcher == (ROOT / "paid_outer_matcher.inc").read_text(encoding="utf8")
    controls = ROOT / "evidence/paid-stream-storage-controls-resume2/VERIFIED.json"
    paidcontrol = read(controls)
    assert paidcontrol["verified"]
    for name, digest in paidcontrol["native_sources_sha256"].items():
        assert sha(ROOT / name) == digest
    librarypath = ROOT / "evidence/n23-portable-outer-obstacles-resume1/LIBRARY.json"
    library = read(librarypath)
    assert library["verified"] and library["all_library_trees_fresh_exact_replayed"]
    assert library["obstacle_count"] == 95 and library["threshold"] == 1
    for relative, digest in library["files"].items():
        assert sha(WORK / relative) == digest
    tablepath = librarypath.parent / "OBSTACLES.tsv"
    assert sha(tablepath) == library["pattern_table_sha256"]
    patterns = library["obstacles"]
    rng = random.Random(2513)
    requests = []
    for pattern in patterns:
        for sign, shift in ((1, 0), (-1, 5), (1, 12)):
            inner = list(range(13, 25))
            rng.shuffle(inner)
            mapping = [(shift+sign*j) % 13 for j in range(13)]+inner[:pattern["centers"]-13]
            faces = sorted(sum(1 << mapping[v] for v in range(pattern["centers"]) if mask >> v & 1)
                           for mask in pattern["faces"])
            requests.append((pattern["id"], faces))
    for pattern in patterns[:3]:
        requests.append((-1, [mask for mask in pattern["faces"] if not mask & 1]))
    requestpath = args.output / "requests.tsv"
    maps = args.output / "maps.json"
    with requestpath.open("x", encoding="ascii") as stream:
        for i, (_, masks) in enumerate(requests):
            stream.write("\t".join(map(str, [i, len(masks), *masks]))+"\n")
    subprocess.run([str(ROOT / "peel_outer_match.exe"), "match", "25", "13",
                    str(tablepath.relative_to(ROOT)), str(requestpath), str(maps)], cwd=ROOT, check=True)
    answers = read(maps)["matches"]
    assert len(answers) == len(requests)
    orientations = set()
    negative = []
    for i, ((expected, faces), result) in enumerate(zip(requests, answers, strict=True)):
        assert result["request"] == i and result["obstacle"] == expected
        if expected < 0:
            negative.append(f"missing-boundary-{i}")
        else:
            mapping = {key: result[key] for key in ("centers", "anchors", "orientation", "shift")}
            check_map(25, 13, patterns[expected], mapping, set(faces), 1)
            orientations.add(mapping["orientation"])
    assert orientations == {-1, 1}
    # Small no-payment search still emits exactly the old complete set.
    oldpath = ROOT / "evidence/paid-matcher-controls-resume1/N8-B6-noscreen-reference.json"
    controlpath = args.output / "N8-B6-empty-library.bin"
    subprocess.run([str(ROOT / "peel_outer_stream.exe"), "8", "6", str(controlpath),
                    "10000000", "804156", "1666328", "2698800", "0", "noscreen", "-"],
                   cwd=ROOT, check=True, stderr=subprocess.DEVNULL)
    header, _ = verify_merge(controlpath)
    assert [row for _, row in BinaryRows(controlpath).rows()] == read(oldpath)["survivors"]
    # A nontrivial complete search with actual outer obstacles.
    referencepath = args.output / "N20-B13-reference.json"
    paidpath = args.output / "N20-B13-paid.bin"
    subprocess.run([str(ROOT / "peel_degree.exe"), "20", "13", str(referencepath),
                    "10000000", "804156", "1666328", "2698800", "0", "dfs"],
                   cwd=ROOT, check=True, stderr=subprocess.DEVNULL)
    subprocess.run([str(ROOT / "peel_outer_stream.exe"), "20", "13", str(paidpath),
                    "10000000", "804156", "1666328", "2698800", "0", "dfs",
                    str(tablepath.relative_to(ROOT))], cwd=ROOT, check=True, stderr=subprocess.DEVNULL)
    paidheader, _ = verify_merge(paidpath)
    residual = {tuple(row["faces"]) for _, row in BinaryRows(paidpath).rows()}
    reference = {tuple(row["faces"]) for row in read(referencepath)["survivors"]}
    assert residual <= reference
    # This independent canonicalizer classifies all lost types, not only samples.
    from group_catalog import canonical
    bycode = {tuple(row["faces"]): row for row in patterns if row["centers"] <= 20}
    paidmaps = []
    for full in sorted(reference-residual):
        code, mapping = canonical(20, 13, list(full), 1)
        assert code in bycode, ("unpaid outer type pruned", full)
        check_map(20, 13, bycode[code], mapping, set(full), 1)
        paidmaps.append({"faces": list(full), "obstacle": bycode[code]["id"], "map": mapping})
    assert len(paidmaps) > 0 and paidheader["proof_prunes"] > 0
    limited = args.output / "limit-no-publication.bin"
    result = subprocess.run([str(ROOT / "peel_outer_stream.exe"), "24", "13", str(limited),
                             "10000000", "788872", "1632237", "2632431", "1", "dfs",
                             str(tablepath.relative_to(ROOT))], cwd=ROOT, capture_output=True)
    assert result.returncode != 0 and not limited.exists()
    negative.append("node-limit-no-publication")
    report = {"verified": True, "outer_kernel_threshold_derivation_verified": True,
              "positive_transformed_maps": 285, "negative_controls_rejected": negative,
              "whole_no_payment_set_checked": header["orbits"],
              "nontrivial_whole_reference_orbits": len(reference),
              "nontrivial_paid_orbits": len(paidmaps), "nontrivial_residual_orbits": len(residual),
              "nontrivial_all_missing_types_paid": True, "paid_type_maps": paidmaps,
              "library_sha256": sha(librarypath), "table_sha256": sha(tablepath),
              "reference_sha256": sha(referencepath), "residual_sha256": sha(paidpath),
              "maps_sha256": sha(maps), "source_sha256": sha(Path(__file__)),
              "native_sources_sha256": {name: sha(ROOT / name) for name in
                  ("peel_outer_stream.cpp", "peel_outer_stream_kernel.inc", "paid_outer_matcher.inc",
                   "paid_stream_storage.inc", "peel_outer_match.cpp")},
              "binary_sha256": sha(ROOT / "peel_outer_stream.exe"),
              "matcher_binary_sha256": sha(ROOT / "peel_outer_match.exe"),
              "reader_sha256": sha(ROOT / "paid_binary_residual.py"),
              "original_storage_controls_sha256": sha(controls),
              "global_optimality_proved": False,
              "scope": "outer pattern guard derivation/maps/nontrivial complete pruning regression"}
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Outer paid controls PASS: 285 maps; complete nontrivial set",
          len(reference), "=", len(paidmaps), "paid +", len(residual), "residual", flush=True)


if __name__ == "__main__":
    main()
