"""Explicit full-type embedding and fresh angle-tree replay for n22 attainment.

This pays the candidate core's lower-bound case, NOT a strict exclusion.
Root and geometric isolation remain separately recorded prerequisites.
"""
from pathlib import Path
from collections import defaultdict
from fractions import Fraction as F
import argparse
import gzip
import json
import exact_graph as exact
from replay_candidate import local
from audit_streamed_hierarchy import check_map, read
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def propose_canonical_map(N, B, masks):
    triangles = [[v for v in range(N) if mask >> v & 1] for mask in masks]
    incidence = defaultdict(list)
    adjacency = [set() for _ in range(N)]
    for i, face in enumerate(triangles):
        assert len(face) == 3
        for v in face:
            adjacency[v].update(w for w in face if w != v)
        for u, v in ((face[0], face[1]), (face[1], face[2]), (face[2], face[0])):
            incidence[tuple(sorted((u, v)))].append(i)
    profiles = [(tuple(len(adjacency[(shift+sign*j) % B]) for j in range(B)), shift, sign)
                for sign in (1, -1) for shift in range(B)]
    minimum = min(p[0] for p in profiles)
    best = mapping = None
    for profile, shift, sign in profiles:
        if profile != minimum:
            continue
        labels = {(shift+sign*j) % B: j for j in range(B)}
        end = (shift+sign) % B
        roots = incidence[tuple(sorted((shift, end)))]
        assert len(roots) == 1
        queue, seen, code = [(roots[0], shift, end)], {roots[0]}, []
        for index, u, v in queue:
            rest = set(triangles[index])-{u, v}
            assert len(rest) == 1
            w = rest.pop()
            if w not in labels:
                labels[w] = len(labels)
            code.append(sum(1 << labels[z] for z in (u, v, w)))
            for a, b in ((v, w), (w, u)):
                unseen = [i for i in incidence[tuple(sorted((a, b)))] if i not in seen]
                assert len(unseen) <= 1
                if unseen:
                    seen.add(unseen[0])
                    queue.append((unseen[0], a, b))
        assert len(seen) == len(masks) and len(labels) == N
        value = tuple(sorted(code))
        if best is None or value < best:
            best = value
            center = [labels[j] for j in range(N)]
            mapping = {"centers": center,
                       "anchors": [(center[0]+sign*j-(sign < 0)) % B for j in range(B)],
                       "orientation": sign, "shift": center[0]}
    assert best is not None
    return list(best), mapping


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--groups", type=Path, required=True)
    ap.add_argument("--tree", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    N, B = 22, 14
    folder = ROOT.parent / "evidence/n22"
    systempath, rootpath = folder / "core-system.json", folder / "core-root.json"
    localpath = folder / "local-isolation-certificate.json"
    constantspath = ROOT.parent / "evidence/core-reduction/constants/n22.json"
    system, root, isolation, constants = map(read, (systempath, rootpath, localpath, constantspath))
    assert (system["N"], system["B"]) == (N, B)
    assert system["center_core_nodes"] == list(range(B, B+N))
    assert sorted(map(tuple, system["active_faces"])) == sorted(map(tuple, system["all_faces"]))
    masks = sorted(sum(1 << v for v in face) for face in system["active_faces"])
    full, mapping = propose_canonical_map(N, B, masks)
    # Independently validate every transferred face and boundary rod.
    check_map(N, B, {"centers": N, "faces": masks}, mapping, set(full), 0)
    data = read(args.groups)
    assert (data["N"], data["B"], data["threshold"]) == (N, B, 0)
    assert data["full_selected_catalog_scanned"]
    found = [g for g in data["groups"] if g["faces"] == full]
    assert len(found) == 1
    group = found[0]
    assert group["centers"] == N and group["members"] == 1
    bindings = args.groups.parent / data["bindings_file"]
    assert sha(bindings) == data["bindings_sha256"]
    selected = []
    with bindings.open(encoding="utf8") as stream:
        for line in stream:
            binding = json.loads(line, object_pairs_hook=no_duplicate_keys)
            if binding["group"] == group["id"]:
                assert binding["map"] == {"centers": list(range(N)), "anchors": list(range(B)),
                                          "orientation": 1, "shift": 0}
                selected.append(binding["index"])
    assert len(selected) == 1
    with gzip.open(args.tree, "rt", encoding="utf8") as stream:
        tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
    assert tree["complete"] and not tree["pending"]
    assert (tree["N"], tree["B"], tree["core_centers"], tree["faces"]) == (N, B, N, masks)
    assert tree["root_sha256"] == sha(rootpath) and tree["system_sha256"] == sha(systempath)
    assert tree["local_sha256"] == sha(localpath) and tree["constants_sha256"] == sha(constantspath)
    paidrootpath = folder / "algebraic-check1/root-verified.json"
    paidroot = read(paidrootpath)
    assert paidroot["verified"] and paidroot["root_sha256"] == isolation["root_sha256"] == sha(rootpath)
    assert paidroot["system_sha256"] == sha(systempath)
    assert isolation["verified"] and F(isolation["isolation_margin"]) > 0
    midpoint = [F(int(v), int(root["Qx"])) for v in root["xnum"]]
    rho = F(1, 10**80)
    anchors = [[(midpoint[2*(i-1)+axis]-rho, midpoint[2*(i-1)+axis]+rho)
                for axis in (0, 1)] for i in range(1, B)]
    result = exact.verify(B, N, masks, tree["nodes"], constants,
                          local=local(anchors, F(isolation["anchor_radius"])))
    result.update(N=N, B=B, full_group=group["id"], catalog_index=selected[0],
                  groups_sha256=sha(args.groups), bindings_sha256=sha(bindings),
                  catalog_sha256=data["catalog_sha256"], tree_sha256=sha(args.tree),
                  candidate_to_full_map=mapping, candidate_face_masks=masks,
                  full_face_masks=full, root_sha256=sha(rootpath),
                  system_sha256=sha(systempath), local_certificate_sha256=sha(localpath),
                  constants_sha256=sha(constantspath), root_report_sha256=sha(paidrootpath),
                  exact_checker_sha256=sha(ROOT / "exact_graph.py"),
                  transfer_checker_sha256=sha(ROOT / "audit_streamed_hierarchy.py"),
                  force_kernel_sha256=sha(ROOT.parent / "round2-grouped/partial_force_exact.py"),
                  source_sha256=sha(Path(__file__)),
                  scope="one explicitly mapped full-type core lower bound, not strict exclusion",
                  root_and_local_prerequisites_not_replayed_here=True,
                  global_optimality_proved=False)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2), encoding="utf8")
    print("N22 explicit attaining-core case + fresh whole-angle replay PASS; group",
          group["id"], "index", selected[0], flush=True)


if __name__ == "__main__":
    main()
