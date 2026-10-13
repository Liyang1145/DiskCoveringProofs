"""Stdlib-only necessary zero-budget ear-cover enumeration."""
from pathlib import Path
from itertools import combinations, product
import sys
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "round3-high"))
from complete_simple_collar import simple_holes, bits
assert __debug__


def ear_branches(N, B, centers, outer, method):
    assert N == centers == 25, "ear cover requires zero new internal center budget at N25"
    holes = simple_holes(centers, B, outer)
    assert holes and method in ("one-per-hole", "two-per-large-hole")
    options = []
    for cycle in holes:
        K = len(cycle)
        ears = [sum(1 << cycle[j] for j in ((i-1) % K, i, (i+1) % K)) for i in range(K)]
        if method == "one-per-hole" or K == 3:
            choices = {(ear,) for ear in ears}
        else:
            choices = {tuple(sorted((ears[i], ears[j]))) for i, j in combinations(range(K), 2)
                       if (i-j) % K not in (1, K-1)}
        assert choices
        options.append(sorted(choices))
    branches, impossible = {}, []
    for chosen in product(*options):
        added = sorted({mask for selection in chosen for mask in selection})
        faces = sorted(set(outer) | set(added))
        incidence = {}
        for mask in faces:
            for edge in combinations(bits(mask), 2):
                incidence.setdefault(edge, []).append(mask)
        bad = next(((edge, masks) for edge, masks in incidence.items() if len(masks) > 2), None)
        if bad is not None:
            edge, masks = bad
            assert len(set(masks[:3])) == 3
            impossible.append({"added_faces": added, "edge": list(edge), "three_faces": masks[:3],
                               "requires_full_simple_disk_condition": True})
        else:
            branches.setdefault(tuple(faces), added)
    return holes, branches, impossible

