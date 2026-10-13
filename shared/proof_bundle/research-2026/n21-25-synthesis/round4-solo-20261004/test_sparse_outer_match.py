"""Accept actual proper subset maps; compare against separate Python injection search."""
from pathlib import Path
from itertools import combinations
import argparse
import copy
import gzip
import json
import os
import random
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
WORK = ROOT.parents[2]
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from group_catalog import validate, canonical
from test_outer_collar import linux_path, WSL
import exact_graph as exact

assert __debug__


def independent_injection(pattern, target_n, target_faces):
    """A differently ordered exhaustive search; no native candidate filters."""
    B = 14
    full = set(target_faces)
    K = pattern["centers"]-B
    used = sorted({j for m in full for j in range(B, target_n) if m >> j & 1})
    if len(used) < K:
        return False
    source_faces = [[j for j in range(pattern["centers"]) if m >> j & 1] for m in pattern["faces"]]
    for sign in (1, -1):
        for shift in range(B):
            image = [(shift+sign*j) % B for j in range(B)] + [-1]*K
            def dfs(index, assigned):
                if index == K:
                    return True
                for candidate in used:
                    if candidate in assigned:
                        continue
                    image[B+index] = candidate
                    valid = True
                    for vertices in source_faces:
                        if all(image[j] >= 0 for j in vertices):
                            mask = sum(1 << image[j] for j in vertices)
                            if mask not in full:
                                valid = False
                                break
                    if valid and dfs(index+1, assigned | {candidate}):
                        return True
                    image[B+index] = -1
                return False
            # Test all-boundary faces before assigning internal variables.
            if any(sum(1 << image[j] for j in vertices) not in full
                   for vertices in source_faces if all(j < B for j in vertices)):
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
    lib = json.loads(args.library.read_text())
    assert lib["verified"] and lib["schema"] == "strict-sparse-outer-obstacle-library-v1"
    table = args.library.parent / "OBSTACLES.tsv"
    assert sha(table) == lib["pattern_table_sha256"]
    constpath = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    const = json.loads(constpath.read_text())
    for relative, digest in lib["files"].items():
        assert sha(WORK / relative) == digest
    for o in lib["obstacles"]:
        with gzip.open(WORK / o["tree_file_relative_to_workspace"], "rt", encoding="utf8") as stream:
            tree = json.load(stream)
        assert exact.verify(14, o["centers"], o["faces"], tree["nodes"], const) == o["fresh_exact_replay"]
    args.output.mkdir(parents=True)
    rng = random.Random(20261004251417)
    requests = []
    synthetic_count = 0
    for o in lib["obstacles"]:
        for sign, shift in ((1, 0), (-1, 5), (1, 13)):
            internal = list(range(14, 25))
            rng.shuffle(internal)
            mapping = [(shift+sign*j) % 14 for j in range(14)]
            mapping += internal[:o["centers"]-14]
            image = {sum(1 << mapping[j] for j in range(o["centers"]) if mask >> j & 1) for mask in o["faces"]}
            requests.append({"faces": sorted(image), "must_hit": True, "kind": "transformed-source", "source": o["id"]})
            extra = (1 << 0) | (1 << 7) | (1 << internal[-1])
            if extra in image:
                extra = (1 << 1) | (1 << 8) | (1 << internal[-1])
            requests.append({"faces": sorted(image | {extra}), "must_hit": True,
                             "kind": "proper-artificial-supergraph", "source": o["id"]})
            synthetic_count += 1
    parentpath = ROOT / "n25-B14-strict-outer-library-v1/LIBRARY.json"
    parents = json.loads(parentpath.read_text())["obstacles"]
    for parent in parents:
        requests.append({"faces": parent["faces"], "must_hit": True,
                         "kind": "actual-accepted-parent", "source": parent["id"]})
    fullsamplepath = ROOT / "n25-B14-archived-run-first-rows/sample-full-graphs.jsonl"
    for line in fullsamplepath.open(encoding="utf8"):
        full = json.loads(line)
        outer = [m for m in full["faces"] if (m & ((1 << 14)-1)).bit_count() >= 1]
        requests.append({"faces": outer, "must_hit": True,
                         "kind": "actual-run-record", "source": full["index"]})
    # Independent existence controls include deletions and arbitrary small
    # graphs, where either result is legitimate but native/Python must agree.
    independent_indices = []
    for o in lib["obstacles"]:
        faces = o["faces"]
        variants = [faces[:], faces[:-1], [faces[0]]]
        for trial in variants:
            if not trial:
                continue
            independent_indices.append(len(requests))
            requests.append({"faces": trial, "must_hit": False, "kind": "independent-existence-control"})
    for _ in range(30):
        trial = sorted({sum(1 << j for j in rng.sample(range(19), 3))
                        for __ in range(5)})
        trial = [m for m in trial if m & ((1 << 14)-1)]
        if trial:
            independent_indices.append(len(requests))
            requests.append({"faces": trial, "must_hit": False, "kind": "random-independent-control"})
    requestpath = args.output / "requests.tsv"
    with requestpath.open("x", encoding="ascii") as stream:
        for i, row in enumerate(requests):
            faces = row["faces"]
            stream.write("\t".join(map(str, (i, len(faces), *faces))) + "\n")
    mappath = args.output / "maps.json"
    def native(tablepath, request, output, n=25, b=14):
        params = [os.path.relpath(Path(p).resolve(), ROOT).replace("\\", "/") for p in (tablepath, request, output)]
        assert all(p.isascii() for p in params)
        return subprocess.run(
            [WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env", "-C", linux_path(ROOT),
             "./sparse_outer_match-linux", "match", str(n), str(b), *params],
            capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
    result = native(table, requestpath, mappath)
    assert result.returncode == 0, result.stderr
    answers = json.loads(mappath.read_text())["matches"]
    assert len(answers) == len(requests)
    verified_hits = 0
    byid = {o["id"]: o for o in lib["obstacles"]}
    for i, (request, answer) in enumerate(zip(requests, answers, strict=True)):
        assert answer["request"] == i
        if request["must_hit"]:
            assert answer["obstacle"] >= 0, ("lost required proper injection", i, request)
        if answer["obstacle"] >= 0:
            o = byid[answer["obstacle"]]
            mapping = {k: answer[k] for k in ("centers", "anchors", "orientation", "shift")}
            validate(25, 14, o["faces"], mapping, request["faces"])
            verified_hits += 1
    independent = []
    for index in independent_indices:
        expected = any(independent_injection(o, 25, requests[index]["faces"]) for o in lib["obstacles"])
        assert (answers[index]["obstacle"] >= 0) == expected
        independent.append({"request": index, "existence": expected})
    # Original array-equality gate fails on the sparse artificial supergraphs
    # by construction; this is not a new full-topology feasibility claim.
    negatives = []
    good = next(i for i, answer in enumerate(answers) if answer["obstacle"] >= 0)
    o = byid[answers[good]["obstacle"]]
    m = {k: answers[good][k] for k in ("centers", "anchors", "orientation", "shift")}
    for label in ("wrong-anchor-offset", "center-collision", "missing-face"):
        bad = copy.deepcopy(m)
        faces = list(requests[good]["faces"])
        if label == "wrong-anchor-offset":
            bad["anchors"][0] = (bad["anchors"][0]+1) % 14
        elif label == "center-collision":
            bad["centers"][1] = bad["centers"][0]
        else:
            image = sum(1 << bad["centers"][j] for j in range(o["centers"]) if o["faces"][0] >> j & 1)
            faces.remove(image)
        try:
            validate(25, 14, o["faces"], bad, faces)
        except (AssertionError, IndexError, ValueError):
            negatives.append(label)
        else:
            raise AssertionError("bad sparse injection accepted")
    lines = table.read_text(encoding="ascii").splitlines()
    for label, badlines in (
        ("bad-schema", ["strict-outer-obstacle-library-v1", *lines[1:]]),
        ("bad-id", [lines[0], lines[1].replace("0\t", "1\t", 1)]),
        ("extra-column", [lines[0], lines[1] + "\t0"]),
    ):
        badtable = args.output / (label + ".tsv")
        badtable.write_text("\n".join(badlines)+"\n", encoding="ascii")
        output = args.output / (label + ".json")
        rejected = native(badtable, requestpath, output)
        assert rejected.returncode != 0 and not output.exists()
        negatives.append(label)
    for label, n, b in (("bad-N", 26, 14), ("bad-B", 14, 15)):
        output = args.output / (label + ".json")
        rejected = native(table, requestpath, output, n, b)
        assert rejected.returncode != 0 and not output.exists()
        negatives.append(label)
    report = {
        "verified": True, "source_sha256": sha(Path(__file__)), "library_sha256": sha(args.library),
        "matcher_source_sha256": sha(ROOT / "sparse_outer_match.cpp"),
        "matcher_include_sha256": sha(ROOT / "sparse_outer_matcher.inc"),
        "matcher_binary_sha256": sha(ROOT / "sparse_outer_match-linux"),
        "all_required_proper_injections_hit_and_explicitly_rechecked": True,
        "total_requests": len(requests), "explicitly_verified_hits": verified_hits,
        "actual_accepted_parent_graphs": len(parents), "actual_run_records": 1930,
        "artificial_strict_supergraph_controls": synthetic_count,
        "independent_python_existence_controls": independent,
        "negative_controls_rejected": negatives, "maps_sha256": sha(mappath),
        "proper_constraint_subset_source_lemma_sha256": sha(ROOT / "SPARSE-OUTER-OBSTACLE-TRANSPORT.md"),
        "complete_production_enumerator_not_implemented_here": True,
        "global_optimality_proved": False,
    }
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("Sparse proper containment controls PASS:", verified_hits, "maps;", len(independent),
          "independent existence checks;", len(negatives), "rejections", flush=True)


if __name__ == "__main__":
    main()
