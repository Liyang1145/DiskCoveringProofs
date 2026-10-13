"""New B14 library transport controls on unchanged native matching/search."""
from pathlib import Path
import argparse
import copy
import gzip
import json
import random
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from audit_streamed_hierarchy import check_map
from stream_catalog import sha
from paid_binary_residual import BinaryRows, verify_merge
from group_catalog import canonical
from n25_outer_search import library_gate, kernel_gate, read, relarg, publish, unchanged

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT.resolve()) and not output.exists()
    const, lib, table, files = library_gate(args.library.resolve())
    kernel_gate(files)
    output.mkdir(parents=True)
    rng = random.Random(202610042514)
    requests = []
    for obstacle in lib["obstacles"]:
        for orientation, shift in ((1, 0), (-1, 5), (1, 13)):
            interior = list(range(14, 25))
            rng.shuffle(interior)
            mapping = [(shift + orientation*i) % 14 for i in range(14)]
            mapping += interior[:obstacle["centers"]-14]
            faces = sorted(sum(1 << mapping[v] for v in range(obstacle["centers"]) if mask >> v & 1)
                           for mask in obstacle["faces"])
            requests.append((obstacle["id"], faces))
    requestpath = output / "requests.tsv"
    with requestpath.open("x", encoding="ascii") as stream:
        for i, (_, faces) in enumerate(requests):
            stream.write("\t".join(map(str, (i, len(faces), *faces))) + "\n")
    mappath = output / "maps.json"
    binary = HIGH / "peel_outer_match.exe"
    subprocess.run([str(binary), "match", "25", "14", relarg(table),
                    relarg(requestpath), relarg(mappath)],
                   cwd=HIGH, check=True, creationflags=subprocess.CREATE_NO_WINDOW)
    answers = read(mappath)["matches"]
    assert len(answers) == len(requests)
    directions = set()
    for i, ((oid, faces), answer) in enumerate(zip(requests, answers, strict=True)):
        assert answer["request"] == i and answer["obstacle"] == oid
        mapping = {k: answer[k] for k in ("centers", "anchors", "orientation", "shift")}
        check_map(25, 14, lib["obstacles"][oid], mapping, set(faces), 1)
        directions.add(mapping["orientation"])
    assert directions == {-1, 1}
    # Complete same-B14 auxiliary-topology control at the SAME U25 angle caps.
    # No N20 covering radius theorem is used.
    referencepath = output / "N20-B14-no-payment-reference.bin"
    paidpath = output / "N20-B14-paid.bin"
    parameters = ["20", "14", str(const["angle_scale"]), *map(str, const["angle_caps"]), "0", "dfs"]
    # peel_degree.exe has incompatible migrated dynamic runtime behavior.
    # The unchanged statically-linked outer kernel with "-" performs the full
    # same recursion with no obstacle pruning; this is a same-kernel control,
    # not an independent enumerator claim.
    subprocess.run([str(HIGH / "peel_outer_stream.exe"), *parameters[:2], relarg(referencepath),
                    *parameters[2:], "-"],
                   cwd=HIGH, check=True, stderr=subprocess.DEVNULL, creationflags=subprocess.CREATE_NO_WINDOW)
    subprocess.run([str(HIGH / "peel_outer_stream.exe"), *parameters[:2], relarg(paidpath),
                    *parameters[2:], relarg(table)],
                   cwd=HIGH, check=True, stderr=subprocess.DEVNULL, creationflags=subprocess.CREATE_NO_WINDOW)
    reference_header, _ = verify_merge(referencepath)
    assert reference_header["proof_prunes"] == 0
    reference = {tuple(row["faces"]) for _, row in BinaryRows(referencepath).rows()}
    _, _ = verify_merge(paidpath)
    residual = {tuple(row["faces"]) for _, row in BinaryRows(paidpath).rows()}
    assert residual <= reference
    bycode = {tuple(o["faces"]): o for o in lib["obstacles"] if o["centers"] <= 20}
    removed_maps = []
    for full in sorted(reference - residual):
        code, mapping = canonical(20, 14, list(full), 1)
        assert code in bycode
        check_map(20, 14, bycode[code], mapping, set(full), 1)
        removed_maps.append({"faces": list(full), "obstacle": bycode[code]["id"], "map": mapping})
    negatives = []
    for label, bad_n, bad_b in (("too-many-centers", 26, 14), ("boundary-over-centers", 14, 15)):
        result = subprocess.run([str(binary), "match", str(bad_n), str(bad_b), relarg(table),
                                 relarg(requestpath), relarg(output / (label + ".json"))],
                                cwd=HIGH, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        assert result.returncode != 0 and not (output / (label + ".json")).exists()
        negatives.append(label)
    tablelines = table.read_text(encoding="ascii").splitlines()
    malformed = {
        "wrong-schema": ["strict-obstacle-library-v1", *tablelines[1:]],
        "bad-first-id": [tablelines[0], tablelines[1].replace("0\t", "1\t", 1)],
        "extra-column": [tablelines[0], tablelines[1] + "\t0"],
    }
    for label, lines in malformed.items():
        badtable = output / (label + ".tsv")
        badtable.write_text("\n".join(lines) + "\n", encoding="ascii")
        result = subprocess.run([str(binary), "match", "25", "14", relarg(badtable),
                                 relarg(requestpath), relarg(output / (label + ".json"))],
                                cwd=HIGH, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
        assert result.returncode != 0 and not (output / (label + ".json")).exists()
        negatives.append(label)
    obstacle = lib["obstacles"][0]
    treepath = ROOT.parents[2] / obstacle["tree_file_relative_to_workspace"]
    with gzip.open(treepath, "rt", encoding="utf8") as stream:
        tree = json.load(stream)
    dual = next(i for i, node in enumerate(tree["nodes"]) if node["kind"] == "DUAL")
    for label in ("zero-flow-scale", "missing-support", "extra-unvisited-node"):
        bad = copy.deepcopy(tree["nodes"])
        if label == "zero-flow-scale":
            bad[dual]["certificate"]["q"] = 0
        elif label == "missing-support":
            bad[dual]["certificate"]["b"].pop()
        else:
            bad.append({"kind": "EMPTY"})
        try:
            exact.verify(14, obstacle["centers"], obstacle["faces"], bad, const)
        except (AssertionError, ValueError, IndexError, KeyError):
            negatives.append(label)
        else:
            raise AssertionError("corrupt mathematical input accepted: " + label)
    limited = output / "node-limit-no-publication.bin"
    command = [str(HIGH / "peel_outer_search_stage.exe"), "25", "14", relarg(limited),
               str(const["angle_scale"]), *map(str, const["angle_caps"]), "1", "dfs", relarg(table), "-", "0"]
    result = subprocess.run(command, cwd=HIGH, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
    assert result.returncode != 0 and not limited.exists() and not Path(str(limited) + ".building").exists()
    negatives.append("node-limit-no-publication")
    unchanged(files)
    publish(output / "VERIFIED.json", {
        "verified": True, "library_sha256": sha(args.library), "pattern_table_sha256": sha(table),
        "source_sha256": sha(Path(__file__)), "search_runner_sha256": sha(ROOT / "n25_outer_search.py"),
        "all_library_transformed_maps_checked": True, "positive_maps": len(answers),
        "complete_same_B14_N20_reference_count": len(reference),
        "complete_same_B14_N20_residual_count": len(residual),
        "reference_kind": "unchanged frozen static recursion without any obstacle table; not an independent enumerator",
        "all_removed_same_B14_control_types_explicitly_paid": True,
        "same_B14_control_removed_maps": removed_maps,
        "same_B14_reference_sha256": sha(referencepath), "same_B14_residual_sha256": sha(paidpath),
        "orientations_checked": sorted(directions), "negative_controls_rejected": negatives,
        "node_limit_cannot_publish": True, "maps_sha256": sha(mappath),
        "matcher_binary_sha256": sha(binary),
        "search_binary_sha256": sha(HIGH / "peel_outer_search_stage.exe"),
        "global_optimality_proved": False,
        "scope": "new B14 library explicit transport and fail-closed controls; not complete n25 enumeration",
    })
    print("N25/B14 library controls PASS:", len(answers), "actual maps;",
          len(negatives), "negative controls", flush=True)


if __name__ == "__main__":
    main()
