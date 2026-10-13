"""Independent missing-type injections for one complete nontrivial paid search."""
from pathlib import Path
from collections import defaultdict
import argparse
import json
from paid_binary_residual import BinaryRows, verify_merge
from stream_catalog import Catalog, sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def check_subset(N, B, pattern, mapping, full):
    center, anchors = mapping["centers"], mapping["anchors"]
    sign, shift = mapping["orientation"], mapping["shift"]
    assert len(center) == pattern["centers"] and len(set(center)) == len(center)
    assert all(type(v) is int and 0 <= v < N for v in center)
    assert sign in (-1, 1) and 0 <= shift < B
    assert center[:B] == [(shift+sign*j) % B for j in range(B)]
    assert all(v >= B for v in center[B:])
    assert anchors == [(shift+sign*j-(sign < 0)) % B for j in range(B)]
    for j in range(B):
        assert {center[j], center[(j+1) % B]} == {anchors[j], (anchors[j]+1) % B}
    assert all(sum(1 << center[v] for v in range(pattern["centers"]) if mask >> v & 1) in full
               for mask in pattern["faces"])


def find_subset(N, B, pattern, full):
    """No canonicalizer: boundary rotations plus bipartite signature injection."""
    signatures = defaultdict(set)
    boundaryfaces = set()
    for face in full:
        boundary = face & ((1 << B)-1)
        internal = face ^ boundary
        if boundary.bit_count() == 3:
            boundaryfaces.add(face)
        elif boundary.bit_count() == 2 and internal.bit_count() == 1:
            signatures[internal.bit_length()-1].add(boundary)
    for sign in (1, -1):
        for shift in range(B):
            centers = [(shift+sign*j) % B for j in range(B)]
            required = defaultdict(set)
            valid = True
            for face in pattern["faces"]:
                boundary = face & ((1 << B)-1)
                image = sum(1 << centers[j] for j in range(B) if boundary >> j & 1)
                internal = face ^ boundary
                if not internal:
                    if image not in boundaryfaces:
                        valid = False
                        break
                else:
                    assert internal.bit_count() == 1
                    required[internal.bit_length()-1].add(image)
            if not valid:
                continue
            domains = {i: [v for v, pairs in signatures.items() if required[i] <= pairs]
                       for i in range(B, pattern["centers"])}
            if any(not values for values in domains.values()):
                continue
            owner = {}
            def augment(i, seen):
                for v in domains[i]:
                    if v in seen:
                        continue
                    seen.add(v)
                    if v not in owner or augment(owner[v], seen):
                        owner[v] = i
                        return True
                return False
            if not all(augment(i, set()) for i in sorted(domains, key=lambda j: len(domains[j]))):
                continue
            assigned = {i: v for v, i in owner.items()}
            centers += [assigned[i] for i in range(B, pattern["centers"])]
            mapping = {"centers": centers, "anchors": [(shift+sign*j-(sign < 0)) % B for j in range(B)],
                       "orientation": sign, "shift": shift}
            check_subset(N, B, pattern, mapping, set(full))
            return mapping
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--reference", type=Path, required=True)
    ap.add_argument("--residual", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    reference = Catalog(args.reference)
    old = {tuple(row["faces"]): row["stabilizer"] for _, row in reference.rows()}
    header, runs = verify_merge(args.residual)
    residual = BinaryRows(args.residual)
    unpaid = {tuple(row["faces"]): row["stabilizer"] for _, row in residual.rows()}
    N, B = header["N"], header["B"]
    assert (N, B) == (reference.header["N"], reference.header["B"])
    assert all(code in old and old[code] == stab for code, stab in unpaid.items())
    librarypath = ROOT / "evidence/n22-portable-strict-obstacles-resume1/LIBRARY.json"
    library = read(librarypath)
    patterns = [row for row in library["obstacles"] if row["B"] == B and row["centers"] <= N]
    byid = {row["id"]: row for row in patterns}
    for payment in header["proof_payments"]:
        mapping = {key: payment[key] for key in ("centers", "anchors", "orientation", "shift")}
        check_subset(N, B, byid[payment["obstacle"]], mapping, set(payment["sample_faces"]))
    paid = []
    for code in sorted(set(old)-set(unpaid)):
        found = None
        for pattern in patterns:
            mapping = find_subset(N, B, pattern, code)
            if mapping is not None:
                found = {"faces": list(code), "obstacle": pattern["id"], "map": mapping}
                break
        assert found is not None, ("unpaid full type incorrectly pruned", code)
        paid.append(found)
    assert len(paid)+len(unpaid) == len(old)
    result = {"verified": True, "N": N, "B": B, "reference_orbits": len(old),
              "paid_orbits_independently_mapped": len(paid), "residual_orbits": len(unpaid),
              "all_missing_types_have_explicit_paid_injections": True,
              "entire_reference_partition_checked": True, "paid_type_maps": paid,
              "native_pruned_states_are_not_orbit_count": header["proof_prunes"],
              "full_binary_run_union_checked": True, "run_sha256": [sha(row.path) for row in runs],
              "reference_sha256": sha(args.reference), "residual_sha256": sha(args.residual),
              "library_sha256": sha(librarypath), "source_sha256": sha(Path(__file__)),
              "global_optimality_proved": False,
              "scope": "nontrivial complete topology-pruning regression only"}
    args.output.write_text(json.dumps(result, indent=2), encoding="utf8")
    print("Complete paid topology regression PASS:", len(old), "=", len(paid),
          "independently paid +", len(unpaid), "residual;", header["proof_prunes"],
          "recursive prunes are not orbit count", flush=True)


if __name__ == "__main__":
    main()
