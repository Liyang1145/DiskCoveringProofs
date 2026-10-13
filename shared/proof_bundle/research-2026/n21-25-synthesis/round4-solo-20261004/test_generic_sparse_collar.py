"""Instantiate proper matching and complete partition controls for n25/B15."""
from pathlib import Path
from copy import deepcopy
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
from family_sparse_gate import sparse_library_gate
from test_outer_collar import linux_path, WSL, collar_codes, run_collar
from test_sparse_collar import run_sparse, mechanical_derivation

assert __debug__


def independent_injection(pattern, target_n, target_faces):
    B, full = pattern["B"], set(target_faces)
    K = pattern["centers"]-B
    available = sorted({v for mask in full for v in range(B, target_n) if mask >> v & 1})
    if len(available) < K:
        return False
    source_faces = [[v for v in range(pattern["centers"]) if mask >> v & 1] for mask in pattern["faces"]]
    for sign in (1, -1):
        for shift in range(B):
            image = [(shift+sign*v) % B for v in range(B)]+[-1]*K
            def dfs(index, used):
                if index == K:
                    return True
                for candidate in available:
                    if candidate in used:
                        continue
                    image[B+index] = candidate
                    if all(sum(1 << image[v] for v in face) in full
                           for face in source_faces if all(image[v] >= 0 for v in face)):
                        if dfs(index+1, used | {candidate}):
                            return True
                    image[B+index] = -1
                return False
            if any(sum(1 << image[v] for v in face) not in full
                   for face in source_faces if all(v < B for v in face)):
                continue
            if dfs(0, set()):
                return True
    return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    constants, library, table, files = sparse_library_gate(args.library.resolve())
    B = library["B"]
    assert B == 15
    mechanical_derivation()
    args.output.mkdir(parents=True)
    rng, requests, independent = random.Random(251510), [], []
    for obstacle in library["obstacles"]:
        for sign, shift in ((1, 0), (-1, B-1), (1, B-2)):
            inner = list(range(B, 25))
            rng.shuffle(inner)
            image = [(shift+sign*v) % B for v in range(B)]+inner[:obstacle["centers"]-B]
            masks = {sum(1 << image[v] for v in range(obstacle["centers"]) if mask >> v & 1)
                     for mask in obstacle["faces"]}
            requests.append((sorted(masks), True))
            extra = (1 << 0) | (1 << (B//2)) | (1 << inner[-1])
            requests.append((sorted(masks | {extra}), True))
        for masks in (obstacle["faces"], obstacle["faces"][:-1], obstacle["faces"][:1]):
            if masks:
                independent.append(len(requests))
                requests.append((masks, False))
    for _ in range(30):
        masks = sorted({sum(1 << v for v in rng.sample(range(B+4), 3)) for j in range(5)})
        masks = [mask for mask in masks if mask & ((1 << B)-1)]
        if masks:
            independent.append(len(requests))
            requests.append((masks, False))
    request_path, map_path = args.output / "requests.tsv", args.output / "maps.json"
    with request_path.open("x", encoding="ascii") as stream:
        for index, (faces, required) in enumerate(requests):
            stream.write("\t".join(map(str, [index, len(faces), *faces]))+"\n")
    relative = lambda path: os.path.relpath(path.resolve(), ROOT).replace("\\", "/")
    result = subprocess.run([
        WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env", "-C", linux_path(ROOT),
        "./sparse_outer_match-linux", "match", "25", str(B),
        relative(table), relative(request_path), relative(map_path),
    ], capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
    assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
    answers = json.loads(map_path.read_text())["matches"]
    assert len(answers) == len(requests)
    byid = {o["id"]: o for o in library["obstacles"]}
    hit_count = 0
    for index, ((faces, required), answer) in enumerate(zip(requests, answers, strict=True)):
        assert answer["request"] == index
        if required:
            assert answer["obstacle"] >= 0
        if answer["obstacle"] >= 0:
            mapping = {key: answer[key] for key in ("centers", "anchors", "orientation", "shift")}
            validate(25, B, byid[answer["obstacle"]]["faces"], mapping, faces)
            hit_count += 1
    for index in independent:
        expected = any(independent_injection(o, 25, requests[index][0]) for o in library["obstacles"])
        assert expected == (answers[index]["obstacle"] >= 0)
    rejected_maps = []
    good = next(index for index, answer in enumerate(answers) if answer["obstacle"] >= 0)
    goodmap = {key: answers[good][key] for key in ("centers", "anchors", "orientation", "shift")}
    obstacle = byid[answers[good]["obstacle"]]
    for label in ("wrong-anchor", "center-collision", "lost-face"):
        mapping, faces = deepcopy(goodmap), list(requests[good][0])
        if label == "wrong-anchor":
            mapping["anchors"][0] = (mapping["anchors"][0]+1) % B
        elif label == "center-collision":
            mapping["centers"][0] = mapping["centers"][1]
        else:
            mask = sum(1 << mapping["centers"][v] for v in range(obstacle["centers"]) if obstacle["faces"][0] >> v & 1)
            faces.remove(mask)
        try:
            validate(25, B, obstacle["faces"], mapping, faces)
        except AssertionError:
            rejected_maps.append(label)
        else:
            raise AssertionError(("bad injection accepted", label))
    maps_controls = args.output / "MATCHING-VERIFIED.json"
    maps_controls.write_text(json.dumps({
        "verified": True, "library_sha256": sha(args.library), "source_sha256": sha(Path(__file__)),
        "matcher_include_sha256": sha(ROOT / "sparse_outer_matcher.inc"),
        "matcher_binary_sha256": sha(ROOT / "sparse_outer_match-linux"),
        "explicit_maps_checked": hit_count, "independent_existence_checks": len(independent),
        "negative_mapping_controls_rejected": rejected_maps, "maps_sha256": sha(map_path),
        "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")
    cases = []
    for N in range(B+4, B+9):
        baseline = args.output / f"N{N}-B{B}-baseline.json"
        result = run_collar(N, B, baseline, "dfs", caps=constants["angle_caps"])
        assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
        _, allcodes = collar_codes(baseline, N, B)
        for mode in ("dfs", "audit"):
            target = args.output / f"N{N}-B{B}-sparse-{mode}.json"
            result = run_sparse(N, B, target, table, mode=mode)
            assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
            header, residual = collar_codes(target, N, B)
            assert residual <= allcodes
            removed = allcodes-residual
            assert all(any(independent_injection(o, N, code) for o in library["obstacles"]) for code in removed)
            for payment in header["sparse_payments"]:
                mapping = {key: payment[key] for key in ("centers", "anchors", "orientation", "shift")}
                validate(N, B, byid[payment["obstacle"]]["faces"], mapping, payment["sample_faces"])
            cases.append({
                "N": N, "B": B, "mode": mode, "baseline_weak_graphs": len(allcodes),
                "residual_weak_graphs": len(residual), "independently_paid_removed_graphs": len(removed),
                "baseline_sha256": sha(baseline), "residual_sha256": sha(target),
            })
        print("B15 complete sparse partition PASS:", N, len(allcodes), "baseline", flush=True)
    disabled = args.output / f"N{B+7}-B{B}-no-sparse.json"
    result = run_sparse(B+7, B, disabled, "-")
    assert result.returncode == 0
    _, actual = collar_codes(disabled, B+7, B)
    _, expected = collar_codes(args.output / f"N{B+7}-B{B}-baseline.json", B+7, B)
    assert actual == expected
    negatives = []
    for label, N, boundary, limit in (("node-limit", 25, B, 1), ("bad-N", 26, B, 0), ("bad-B", B, B+1, 0)):
        target = args.output / (label+".json")
        result = run_sparse(N, boundary, target, table, limit=limit)
        assert result.returncode != 0 and not target.exists()
        negatives.append(label)
    (args.output / "VERIFIED.json").write_text(json.dumps({
        "verified": True, "source_sha256": sha(Path(__file__)),
        "native_source_sha256": sha(ROOT / "peel_sparse_outer_collar.cpp"),
        "native_binary_sha256": sha(ROOT / "peel_sparse_outer_collar-linux"),
        "sparse_guard_sha256": sha(ROOT / "sparse_outer_matcher.inc"),
        "library_sha256": sha(args.library),
        "proper_matching_controls_sha256": sha(maps_controls),
        "all_baseline_minus_residual_graphs_independently_paid": True,
        "no_sparse_guard_full_set_equal": True, "cases": cases,
        "negative_controls_rejected": negatives, "global_optimality_proved": False,
    }, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
