"""Check topology-conditioned payments over all paid full completion types."""
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
from stream_catalog import sha, no_duplicate_keys
from group_catalog import validate, canonical
from cross_order_strict_transfer import validate_disk
from n25_outer_search import read, publish, bind, unchanged
from complete_simple_collar import simple_holes
from completion_family_gate import library_gate, validate_outer_payment
from derive_completion_matcher import derive
from test_generic_sparse_collar import independent_injection
from test_outer_collar import linux_path, WSL

assert __debug__


def derivation_gate():
    report = read(ROOT / "completion-matcher-source-derivation.json")
    assert report["verified_mechanical_derivation"]
    assert report["original_matcher_sha256"] == sha(ROOT / "sparse_outer_matcher.inc")
    assert report["derived_matcher_sha256"] == sha(ROOT / "completion_family_matcher.inc")
    assert report["source_sha256"] == sha(ROOT / "derive_completion_matcher.py")
    source = (ROOT / "sparse_outer_matcher.inc").read_text(encoding="utf8")
    expected, names, changes = derive(source)
    assert report["identifier_renames"] == names and report["explicit_changes"] == [list(v) for v in changes]
    assert expected == (ROOT / "completion_family_matcher.inc").read_text(encoding="utf8")


def native(table, requests, output, B, N=25):
    inputpath, answerpath = output / "REQUESTS.tsv", output / "NATIVE-MAPS.json"
    assert not inputpath.exists() and not answerpath.exists()
    with inputpath.open("x", encoding="ascii") as stream:
        for index, faces in enumerate(requests):
            stream.write("\t".join(map(str, [index, len(faces), *faces]))+"\n")
    relative = lambda p: os.path.relpath(p.resolve(), ROOT).replace("\\", "/")
    result = subprocess.run([
        WSL, "--distribution", "Ubuntu2204", "--exec", "/usr/bin/env", "-C", linux_path(ROOT),
        "./completion_family_match-linux", str(N), str(B),
        relative(table), relative(inputpath), relative(answerpath),
    ], capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
    publish(output / "NATIVE-TERMINAL.json", {
        "actual_exit_code": result.returncode, "stdout": result.stdout.decode("utf8", errors="replace"),
        "stderr": result.stderr.decode("utf8", errors="replace"), "N": N, "B": B,
        "maps_are_only_proposals": True,
    })
    return result, answerpath


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    derivation_gate()
    library, table, files = library_gate(args.library.resolve())
    output.mkdir()
    rng = random.Random(251416)
    pattern_byid = {p["id"]: p for p in library["patterns"]}
    summaries, rejected = [], []
    total_full = total_native = exact_known = 0
    for pattern in library["patterns"]:
        B, centers, faces = pattern["B"], pattern["centers"], pattern["faces"]
        case_root = output / f"B{B}"
        case_root.mkdir()
        requests, kinds, required, must_miss, independent_indices = [], [], [], [], []
        for sign in (1, -1):
            for shift in range(B):
                interior = list(range(B, 25))
                rng.shuffle(interior)
                center = [(shift+sign*v) % B for v in range(B)]+interior[:centers-B]
                mapping = {"centers": center,
                           "anchors": [(shift+sign*v-(sign < 0)) % B for v in range(B)],
                           "orientation": sign, "shift": shift}
                image = sorted(sum(1 << center[v] for v in range(centers) if mask >> v & 1) for mask in faces)
                validate_outer_payment(pattern, 25, B, image, mapping)
                required.append(len(requests))
                requests.append(image)
                kinds.append("all-dihedral-raw-injections")
        independent_indices.append(len(requests))
        required.append(len(requests))
        requests.append(faces)
        kinds.append("source-pattern")
        for trial, kind in ((faces[:-1], "missing-face"),
                            (sorted(faces+[next((1 << i) | (1 << j) | (1 << 24)
                                               for i in range(B) for j in range(i+1, B)
                                               if ((1 << i) | (1 << j) | (1 << 24)) not in faces)]),
                             "extra-outer-face")):
            assert trial == sorted(set(trial))
            must_miss.append(len(requests))
            independent_indices.append(len(requests))
            requests.append(trial)
            kinds.append(kind)
        # Mutate one face without altering its cardinality. The native result
        # is compared with an independently ordered exhaustive injection.
        for oldmask in faces[:4]:
            original = [v for v in range(centers) if oldmask >> v & 1]
            replacement = next(v for v in range(25) if v not in original)
            mutated = (oldmask ^ (1 << original[-1])) | (1 << replacement)
            trial = sorted(set((set(faces)-{oldmask}) | {mutated}))
            if trial and all(mask & ((1 << B)-1) for mask in trial):
                independent_indices.append(len(requests))
                requests.append(trial)
                kinds.append("mutated-face-existence-control")
        closure = read(ROOT / pattern["closure_file_relative_to_library"])
        # Locate the source catalog from its frozen closure bindings.
        paths = [ROOT.parents[2] / rel for rel in closure["files_relative_to_workspace"]
                 if rel.endswith("/GROUPS.json") and "simple-hole-completions" in rel]
        assert len(paths) == 1
        groupspath = paths[0]
        groups = read(groupspath)
        assert groups["group_count"] == pattern["full_completion_types_paid"]
        full_start = len(requests)
        for group in groups["groups"]:
            outer = [mask for mask in group["faces"] if mask & ((1 << B)-1)]
            required.append(len(requests))
            requests.append(outer)
            kinds.append("paid-full-completion")
        result, answerpath = native(table, requests, case_root, B)
        assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
        response = read(answerpath)
        assert response["scope"] == "N25 equal-outer-face topology-conditioned payment maps only"
        answers = response["matches"]
        assert len(answers) == len(requests)
        accepted = []
        for index, answer in enumerate(answers):
            assert answer["request"] == index
            if index in required:
                assert answer["pattern"] == pattern["id"], ("a paid exact outer fan was lost", B, index)
            if index in must_miss:
                assert answer["pattern"] == -1
            if answer["pattern"] >= 0:
                source_pattern = pattern_byid[answer["pattern"]]
                mapping = {key: answer[key] for key in ("centers", "anchors", "orientation", "shift")}
                result = validate_outer_payment(source_pattern, 25, B, requests[index], mapping)
                accepted.append({"request": index, "pattern": answer["pattern"], "map": mapping,
                                 "lower_mode": result["lower_mode"]})
                total_native += 1
        for index in independent_indices:
            used = set(v for mask in requests[index] for v in range(25) if mask >> v & 1)
            expected = (len(requests[index]) == len(faces) and len(used) == centers
                        and independent_injection(pattern, 25, requests[index]))
            assert (answers[index]["pattern"] >= 0) == expected
        # Check the payment against every full disk, including all pure inner
        # faces; the equality of source/target outer fans is essential.
        for gid, group in enumerate(groups["groups"]):
            answer = answers[full_start+gid]
            mapping = {key: answer[key] for key in ("centers", "anchors", "orientation", "shift")}
            validate_disk(25, B, group["faces"])
            validate(25, B, faces, mapping, group["faces"])
            image = {sum(1 << mapping["centers"][v] for v in range(centers) if mask >> v & 1)
                     for mask in faces}
            assert image == {mask for mask in group["faces"] if mask & ((1 << B)-1)}
            total_full += 1
            if B == 16 and gid == closure["attaining_group"]:
                assert pattern["lower_mode"] == "no_full_simple_disk_realization_with_all_rods_strictly_below_exact_rstar"
                exact_known += 1
        (case_root / "ACCEPTED-MAPS.jsonl").write_text(
            "".join(json.dumps(row, separators=(",", ":"))+"\n" for row in accepted), encoding="utf8")
        base_answer = answers[0]
        base_map = {key: base_answer[key] for key in ("centers", "anchors", "orientation", "shift")}
        for label in ("wrong-N", "wrong-B", "center-collision", "anchor-offset", "extra-face"):
            mapping, n, target_B, target = deepcopy(base_map), 25, B, list(requests[0])
            if label == "wrong-N":
                n = 24
            elif label == "wrong-B":
                target_B = B-1
            elif label == "center-collision":
                mapping["centers"][1] = mapping["centers"][0]
            elif label == "anchor-offset":
                mapping["anchors"][0] = (mapping["anchors"][0]+1) % B
            else:
                extra = next((1 << i) | (1 << j) | (1 << 24)
                             for i in range(B) for j in range(i+1, B)
                             if ((1 << i) | (1 << j) | (1 << 24)) not in target)
                target = sorted(target+[extra])
            try:
                validate_outer_payment(pattern, n, target_B, target, mapping)
            except (AssertionError, IndexError):
                rejected.append(f"B{B}-{label}")
            else:
                raise AssertionError(("invalid completion payment accepted", B, label))
        summaries.append({
            "B": B, "source_pattern": pattern["id"], "all_2B_boundary_maps_checked": True,
            "native_proposed_maps_explicitly_validated": len(accepted),
            "complete_paid_full_types_transported": groups["group_count"],
            "independent_existence_controls": len(independent_indices),
            "strict_geometric_weak_exclusion_not_claimed": True,
            "native_maps_sha256": sha(answerpath),
            "accepted_maps_sha256": sha(case_root / "ACCEPTED-MAPS.jsonl"),
            "full_catalog_sha256": sha(groupspath),
        })
        bind(files, groupspath)
        print("Completion-family transports accepted: B", B, groups["group_count"], "full types", flush=True)
    # Reject applying the fixed-order theorem to any other n, and wrong schemas.
    for label, N, wrong_schema in (("native-wrong-N", 24, False), ("native-wrong-schema", 25, True)):
        root = output / label
        root.mkdir()
        tab = table
        if wrong_schema:
            tab = root / "WRONG-TABLE.tsv"
            text = table.read_text(encoding="ascii")
            tab.write_text(text.replace("paid-simple-collar-completion-library-v1",
                                       "strict-sparse-outer-obstacle-library-v1", 1), encoding="ascii")
        p = library["patterns"][0]
        result, answerpath = native(tab, [p["faces"]], root, p["B"], N)
        assert result.returncode != 0 and not answerpath.exists()
        rejected.append(label)
    for path in (Path(__file__), args.library, ROOT / "completion_family_gate.py",
                 ROOT / "completion_family_match.cpp", ROOT / "completion_family_match-linux",
                 ROOT / "completion_family_matcher.inc", ROOT / "derive_completion_matcher.py",
                 ROOT / "completion-matcher-source-derivation.json", HIGH / "group_catalog.py"):
        bind(files, path)
    unchanged(files)
    assert total_full == 8385+91 and exact_known == 1
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "completion-family-equal-outer-map-controls-v1",
        "source_sha256": sha(Path(__file__)), "library_sha256": sha(args.library),
        "native_matcher_source_sha256": sha(ROOT / "completion_family_match.cpp"),
        "native_matcher_binary_sha256": sha(ROOT / "completion_family_match-linux"),
        "matcher_include_sha256": sha(ROOT / "completion_family_matcher.inc"),
        "derivation_sha256": sha(ROOT / "completion-matcher-source-derivation.json"),
        "all_8476_paid_full_completion_types_transported": True,
        "explicitly_verified_full_type_maps": total_full,
        "all_successful_native_maps_explicitly_checked": total_native,
        "known_attaining_type_paid_only_as_exact_core_lower_bound": exact_known,
        "patterns": summaries, "negative_controls_rejected": rejected,
        "files_relative_to_workspace": files, "global_optimality_proved": False,
        "complete_production_search_not_run_here": True,
    })


if __name__ == "__main__":
    main()
