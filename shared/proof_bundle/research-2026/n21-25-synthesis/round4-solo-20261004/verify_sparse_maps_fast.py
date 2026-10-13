"""Fresh strict-library acceptance plus explicit, batch-checked injections.

Native matches are only witnesses. Python checks every successful center,
anchor and face map. Failure to find a match is never a proof of exclusion.
"""
from pathlib import Path
from copy import deepcopy
from collections import Counter
import argparse
import json
import os
import random
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import validate
from n25_outer_search import read, bind, unchanged, publish
from test_outer_collar import linux_path, WSL
from test_generic_sparse_collar import independent_injection

assert __debug__


def library_gate(path):
    data = read(path)
    if data["B"] == 14 and data["source_sha256"] == sha(ROOT / "export_sparse_outer_library.py"):
        from run_sparse_collar import sparse_library_gate
    else:
        from family_sparse_gate import sparse_library_gate
    return sparse_library_gate(path)


def batch_match(table, requests, output, N, B):
    requestpath, answerpath = output / "REQUESTS.tsv", output / "NATIVE-MAPS.json"
    assert not requestpath.exists() and not answerpath.exists()
    with requestpath.open("x", encoding="ascii", newline="\n") as stream:
        for index, faces in enumerate(requests):
            assert faces == sorted(set(faces)) and faces
            stream.write("\t".join(map(str, [index, len(faces), *faces]))+"\n")
    relative = lambda path: os.path.relpath(path.resolve(), ROOT).replace("\\", "/")
    assert all(relative(path).isascii() for path in (table, requestpath, answerpath))
    command = [
        WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env", "-C", linux_path(ROOT),
        "./sparse_outer_match-linux", "match", str(N), str(B),
        relative(table), relative(requestpath), relative(answerpath),
    ]
    result = subprocess.run(command, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
    publish(output / "NATIVE-TERMINAL.json", {
        "actual_exit_code": result.returncode, "command": command,
        "stdout": result.stdout.decode("utf8", errors="replace"),
        "stderr": result.stderr.decode("utf8", errors="replace"),
        "maps_are_only_witness_proposals": True,
    })
    assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
    data = read(answerpath)
    assert data["scope"] == "sparse subgraph maps only"
    answers = data["matches"]
    assert [row["request"] for row in answers] == list(range(len(requests)))
    return answers


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    constants, library, table, files = library_gate(args.library.resolve())
    B = library["B"]
    output.mkdir()
    rng = random.Random(251714)
    requests, required, independent = [], [], []
    for obstacle in library["obstacles"]:
        for sign, shift in ((1, 0), (-1, B-1), (1, B//2)):
            inner = list(range(B, 25))
            rng.shuffle(inner)
            center = [(shift+sign*v) % B for v in range(B)]+inner[:obstacle["centers"]-B]
            mapping = {"centers": center,
                       "anchors": [(shift+sign*v-(sign < 0)) % B for v in range(B)],
                       "orientation": sign, "shift": shift}
            images = {sum(1 << center[v] for v in range(obstacle["centers"]) if face >> v & 1)
                      for face in obstacle["faces"]}
            validate(25, B, obstacle["faces"], mapping, images)
            required.append(len(requests))
            requests.append(sorted(images))
            extra = next((1 << i) | (1 << j) | (1 << inner[-1])
                         for i in range(B) for j in range(i+1, B)
                         if ((1 << i) | (1 << j) | (1 << inner[-1])) not in images)
            required.append(len(requests))
            requests.append(sorted(images | {extra}))
        for faces in (obstacle["faces"], obstacle["faces"][:-1], obstacle["faces"][:1]):
            if faces:
                independent.append(len(requests))
                requests.append(faces)
    for _ in range(30):
        faces = sorted({sum(1 << v for v in rng.sample(range(min(B+5, 25)), 3)) for j in range(5)})
        faces = [face for face in faces if face & ((1 << B)-1)]
        if faces:
            independent.append(len(requests))
            requests.append(faces)
    known = None
    if B == 16:
        geometry = read(ROOT.parent / "evidence/n25-algebraic-upper-round2/geometry.json")
        known = len(requests)
        requests.append(sorted(sum(1 << v for v in face) for face in geometry["faces"] if any(v < B for v in face)))
    answers = batch_match(table, requests, output, 25, B)
    byid = {o["id"]: o for o in library["obstacles"]}
    hit_count = 0
    for index, answer in enumerate(answers):
        if index in required:
            assert answer["obstacle"] >= 0
        if answer["obstacle"] >= 0:
            obstacle = byid[answer["obstacle"]]
            mapping = {key: answer[key] for key in ("centers", "anchors", "orientation", "shift")}
            validate(25, B, obstacle["faces"], mapping, requests[index])
            hit_count += 1
    if known is not None:
        assert answers[known]["obstacle"] == -1, "strict library matched known attaining graph"
    for index in independent:
        expected = any(independent_injection(o, 25, requests[index]) for o in library["obstacles"])
        assert expected == (answers[index]["obstacle"] >= 0)
    good = next(index for index, row in enumerate(answers) if row["obstacle"] >= 0)
    obstacle = byid[answers[good]["obstacle"]]
    base_map = {key: answers[good][key] for key in ("centers", "anchors", "orientation", "shift")}
    rejected = []
    for label in ("wrong-anchor-offset", "center-collision", "missing-image-face"):
        mapping, faces = deepcopy(base_map), list(requests[good])
        if label == "wrong-anchor-offset":
            mapping["anchors"][0] = (mapping["anchors"][0]+1) % B
        elif label == "center-collision":
            mapping["centers"][0] = mapping["centers"][1]
        else:
            image = sum(1 << mapping["centers"][v] for v in range(obstacle["centers"]) if obstacle["faces"][0] >> v & 1)
            faces.remove(image)
        try:
            validate(25, B, obstacle["faces"], mapping, faces)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("bad witness accepted", label))
    for path in (Path(__file__), ROOT / "test_generic_sparse_collar.py",
                 ROOT / "sparse_outer_match.cpp", ROOT / "sparse_outer_match-linux",
                 ROOT / "sparse_outer_matcher.inc", HIGH / "group_catalog.py"):
        bind(files, path)
    unchanged(files)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "fresh-sparse-library-explicit-map-controls-v1",
        "N": 25, "B": B, "library_sha256": sha(args.library),
        "source_sha256": sha(Path(__file__)),
        "all_source_trees_fresh_exact_replayed": True,
        "explicitly_checked_native_maps": hit_count,
        "independent_python_existence_controls": len(independent),
        "required_transformed_and_proper_supergraph_maps": len(required),
        "known_B16_attaining_graph_not_matched": known is not None,
        "negative_controls_rejected": rejected,
        "matcher_include_sha256": sha(ROOT / "sparse_outer_matcher.inc"),
        "matcher_source_sha256": sha(ROOT / "sparse_outer_match.cpp"),
        "matcher_binary_sha256": sha(ROOT / "sparse_outer_match-linux"),
        "native_maps_sha256": sha(output / "NATIVE-MAPS.json"),
        "files_relative_to_workspace": files,
        "global_optimality_proved": False,
    })
    print("Fresh B", B, "sparse map controls accepted:", hit_count, "explicit maps;",
          len(independent), "independent existence checks", flush=True)


if __name__ == "__main__":
    main()
