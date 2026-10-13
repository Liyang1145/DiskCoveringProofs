"""Canonical form for dual-disk complexes with a PROVABLE invariance property.

A complex here is a tuple of face-triples with vertices 0..N-1 (ring) and N..N+m-1 (hubs).
The relevant isomorphism group is exactly G = D_N x S_m acting by
    ring  v -> (eps*v + sh) mod N,   eps in {+1,-1}, sh in Z_N
    hub   N+j -> N+perm(j)
(ring relabelings are the dihedral group of the N-cycle; hub relabelings are all of S_m).

canon_true(faces) = min over all 2N*|S_m| elements of the orbit of the sorted face tuple.
Taking a minimum over a group orbit is invariant BY CONSTRUCTION: applying any g in G to the
input just permutes the orbit, leaving the minimum fixed.  This is the property that must be
verified; the test below checks it explicitly on the enumerated classes.

canon_lead replicates the lead's full_canon convention (hub relabelling by order of first
appearance in cyclic vertex-index order, then min over 2N ring maps) so that its invariance
can be tested separately.
"""
import itertools
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def canon_true(N, m, faces):
    faces = [tuple(sorted(f)) for f in faces]
    best = None
    perms = list(itertools.permutations(range(m)))
    for perm in perms:
        relab = [None] * (N + m)
        for v in range(N):
            relab[v] = v
        for j in range(m):
            relab[N + j] = N + perm[j]
        rel = [tuple(sorted(relab[v] for v in f)) for f in faces]
        for sh in range(N):
            for eps in (1, -1):
                img = []
                for f in rel:
                    o = []
                    for v in f:
                        if v < N:
                            o.append((eps * v + sh) % N)
                        else:
                            o.append(v)
                    img.append(tuple(sorted(o)))
                key = tuple(sorted(img))
                if best is None or key < best:
                    best = key
    return best


def canon_lead(N, m, faces):
    """replica of members/topology/gen_k10_catalogue.py full_canon"""
    faces = [tuple(sorted(f)) for f in faces]
    best = None
    for perm in itertools.permutations(range(m)):
        relab = tuple(N + perm[v - N] if v >= N else v for v in range(N + m))
        for sh in range(N):
            for refl in (False, True):
                img = []
                for f in faces:
                    out = []
                    for v in f:
                        w = relab[v]
                        if w < N:
                            x = (w + sh) % N
                            if refl:
                                x = (sh - (w - sh)) % N
                            out.append(x)
                        else:
                            out.append(w)
                    img.append(tuple(sorted(out)))
                key = tuple(sorted(img))
                if best is None or key < best:
                    best = key
    return best


def apply_group(N, m, faces, eps, sh, perm):
    out = []
    for f in faces:
        o = []
        for v in f:
            if v < N:
                o.append((eps * v + sh) % N)
            else:
                o.append(N + perm[v - N])
        out.append(tuple(sorted(o)))
    return tuple(sorted(out))


def invariance_test(N, m, classes, limit=12, seed=0):
    """check canon_true and canon_lead invariance under every g in G, on a sample"""
    res = {"canon_true_violations": 0, "canon_lead_violations": 0,
           "canon_true_values_lead_violations": 0, "samples": 0}
    perms = list(itertools.permutations(range(m)))
    maps = []
    for sh in range(N):
        for eps in (1, -1):
            for perm in perms:
                maps.append((eps, sh, perm))
    step = max(1, len(classes) // limit)
    for i in range(0, len(classes), step):
        faces = list(classes[i])
        c0 = canon_true(N, m, faces)
        c0l = canon_lead(N, m, faces)
        res["samples"] += 1
        badT = badL = 0
        for eps, sh, perm in maps:
            g = list(apply_group(N, m, faces, eps, sh, perm))
            if canon_true(N, m, g) != c0:
                badT += 1
            if canon_lead(N, m, g) != c0l:
                badL += 1
        if badT:
            res["canon_true_violations"] += 1
        if badL:
            res["canon_lead_violations"] += 1
        if badT or badL:
            res.setdefault("examples", []).append(
                dict(index=i, bad_true=badT, bad_lead=badL))
    return res


if __name__ == "__main__":
    N = int(sys.argv[1])
    m = int(sys.argv[2])
    d = json.loads((HERE / "evidence" / ("indep-enum-N%d-m%d.json" % (N, m))).read_text(
        encoding="utf-8"))
    classes = [json.loads(s) for s in d["classes"]]
    t = invariance_test(N, m, classes)
    print("invariance_test", json.dumps(t, indent=1)[:2000])
    kt = set(canon_true(N, m, c) for c in classes)
    kl = set(canon_lead(N, m, c) for c in classes)
    print("raw valid complexes (phase1 already deduped by my cheap key):", len(classes))
    print("canon_true classes:", len(kt))
    print("canon_lead classes:", len(kl))
    (HERE / "evidence" / ("canon-test-N%d-m%d.json" % (N, m))).write_text(
        json.dumps({"invariance": t, "n_phase1": len(classes),
                    "canon_true": len(kt), "canon_lead": len(kl)}, indent=1),
        encoding="utf-8")
