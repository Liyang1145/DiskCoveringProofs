"""Enumerate the possible equality pattern of the B=14 boundary-face apices."""
from collections import Counter
from itertools import product
from pathlib import Path
import argparse
import json

B=14
NORM_CEILING=912_615_794


def apex_norm_ceiling(count):
    return {11:892_960_000,12:876_600_000}.get(count,NORM_CEILING)


def minimum_boundary_neighbors(low):
    if low>=905_600_000:
        return 10
    if low>=833_896_000:
        return 9
    return 8


def distance(a,b):
    d=(a-b)%B
    return min(d,B-d)


def neighbor_sets(faces):
    return {i for e in faces for i in (e,(e+1)%B)}


def plausible(faces):
    owners=neighbor_sets(faces)
    return all(distance(a,b)<=2 for a in owners for b in owners)


def partitions():
    """Each repeated apex is used on two consecutive boundary edges."""
    available=[(i,(i+1)%B) for i in range(B)]
    for choose in product((False,True),repeat=B):
        chosen=[p for p,keep in zip(available,choose) if keep]
        labels=[i for pair in chosen for i in pair]
        if len(set(labels))!=len(labels):
            continue
        used=set(labels)
        blocks=chosen+[(i,) for i in range(B) if i not in used]
        # Fourteen boundary faces, each apex on one or two of them.
        # The lower bound eight applies to all internal neighbors of the
        # boundary, including vertices not used by a boundary face.
        if not 7<=len(blocks)<=12:
            continue
        yield tuple(sorted(tuple(sorted(x)) for x in blocks))


def verify():
    # Independently classify all feasible nonsingleton subsets before
    # using the explicit recurrence. No unverified symmetry reduction.
    pairs=set()
    for bits in range(1,1<<B):
        edges=tuple(i for i in range(B) if bits>>i&1)
        if len(edges)<2 or not plausible(edges):
            continue
        if len(edges)==2:
            pairs.add(edges)
        else:
            raise ValueError("unexpected repeated apex on three or more edges")
    adjacent={tuple(sorted((i,(i+1)%B))) for i in range(B)}
    if pairs!=adjacent:
        raise ValueError("incorrect apex block classification")
    patterns=sorted(set(partitions()))
    counts=Counter(map(len,patterns))
    return patterns,counts


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    pats,counts=verify()
    for n,count in sorted(counts.items()):
        print(f"{n} apex centers: {count}; outer norm ceiling {apex_norm_ceiling(n)}/1e9.")
    for low in (833_896_000, 876_600_000, 892_960_000, 905_600_000):
        allowed=sum(count for n,count in counts.items() if apex_norm_ceiling(n)>low)
        print(f"D1 >= {low}/1e9: {allowed} patterns, at least {minimum_boundary_neighbors(low)} interior boundary neighbors.")
    print(f"PASS B=14: {len(pats)} boundary-apex partitions.")
    if args.output:
        args.output.write_text(json.dumps({"patterns":pats},separators=(",",":"))+"\n",
                               encoding="utf-8")
